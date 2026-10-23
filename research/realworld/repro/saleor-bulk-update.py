"""Repro for inventory/saleor/allocations' refuted laws: a deallocation of two order lines on one stock.

Saleor 3.23.44 (saleor/saleor@b2587a12ea15edf3432aaa4c6a5065c9c9ca049f, BSD-3-Clause, (c) Saleor Commerce) needs its
whole app and Postgres to run deallocate_stock, so this runs the part that decides the outcome on Django itself, at
the version Saleor pins (pyproject.toml:26 "django[bcrypt]~=5.2.18"), with SQLite: Saleor's Stock and Allocation
fields (saleor/warehouse/models.py:527-597, trimmed to the columns used) and deallocate_stock's loop and writes
(saleor/warehouse/management.py:390-449, excerpted below with the lock, the events and the error path left out).
In management.py, `allocation_with_stock_qs_select_for_update()` is `Allocation.objects.select_related("stock")...
.order_by("stock__pk")` (lock_objects.py), so each allocation carries its own Stock instance, and the stocks list
gets one instance per allocation deallocated.

  uv run --no-project --with 'django~=5.2.18' python -I research/realworld/repro/saleor-bulk-update.py
"""
import django
from django.conf import settings

# The models borrow an installed app's label (contenttypes) so no app package is needed.
settings.configure(
    INSTALLED_APPS=["django.contrib.contenttypes"],
    DATABASES={"default": {"ENGINE": "django.db.backends.sqlite3", "NAME": ":memory:"}},
    DEFAULT_AUTO_FIELD="django.db.models.AutoField",
)
django.setup()

from django.db import connection, models
from django.db.models import F


class Stock(models.Model):  # models.py:527-533
    quantity = models.IntegerField(default=0)
    quantity_allocated = models.IntegerField(default=0)

    class Meta:
        app_label = "contenttypes"
        ordering = ("pk",)


class Allocation(models.Model):  # models.py:573-597
    order_line = models.IntegerField()
    stock = models.ForeignKey(Stock, on_delete=models.CASCADE, related_name="allocations")
    quantity_allocated = models.PositiveIntegerField(default=0)

    class Meta:
        app_label = "contenttypes"
        unique_together = [["order_line", "stock"]]
        ordering = ("pk",)


with connection.schema_editor() as editor:
    editor.create_model(Stock)
    editor.create_model(Allocation)


def deallocate_stock(order_lines_data):
    """management.py:383-449, without select_for_update, the back-in-stock events and the AllocationError path."""
    lines = [line for line, _ in order_lines_data]
    lines_allocations = Allocation.objects.select_related("stock").filter(order_line__in=lines).order_by("stock__pk")
    line_to_allocations = {}
    for allocation in lines_allocations:
        line_to_allocations.setdefault(allocation.order_line, []).append(allocation)
    allocations_to_update = []
    stocks_to_update = []
    for order_line, quantity in order_lines_data:
        allocations = line_to_allocations.get(order_line, [])
        quantity_dealocated = 0
        for allocation in allocations:
            quantity_to_deallocate = min((quantity - quantity_dealocated), allocation.quantity_allocated)
            if quantity_to_deallocate > 0:
                allocation.quantity_allocated = allocation.quantity_allocated - quantity_to_deallocate
                stock = allocation.stock
                stock.quantity_allocated = F("quantity_allocated") - quantity_to_deallocate
                stocks_to_update.append(stock)
                quantity_dealocated += quantity_to_deallocate
                allocations_to_update.append(allocation)
                if quantity_dealocated == quantity:
                    break
    Allocation.objects.bulk_update(allocations_to_update, ["quantity_allocated"])
    Stock.objects.bulk_update(stocks_to_update, ["quantity_allocated"])


def show(label):
    s = Stock.objects.get()
    total = sum(a.quantity_allocated for a in Allocation.objects.all())
    print(f"{label}: stock.quantity_allocated={s.quantity_allocated}, sum of allocations={total}")


print("django", django.get_version())
stock = Stock.objects.create(quantity=10, quantity_allocated=5)
Allocation.objects.create(order_line=1, stock=stock, quantity_allocated=2)
Allocation.objects.create(order_line=2, stock=stock, quantity_allocated=3)
show("allocated: line 1 has 2, line 2 has 3")
deallocate_stock([(1, 2), (2, 3)])
show("after deallocate_stock for both lines")
s = Stock.objects.get()
print("quantity_allocated equals the allocations:", s.quantity_allocated == 0, "(it lost the second line's decrement)" if s.quantity_allocated == 3 else "")
