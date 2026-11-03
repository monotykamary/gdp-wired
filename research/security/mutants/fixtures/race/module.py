# The declared isolation is part of this module's deployment contract.
# gdp: env atomic
class Payments:
    def __init__(self, cache, gateway):
        self.cache = cache
        self.gateway = gateway

    # gdp: law one charge per order: at most one call between pay and pay
    def pay(self, order: str, amount: int) -> None:
        if self.cache.get(order) is not None:
            return
        self.gateway.charge(order, amount)  # gdp: effect
        self.cache.set(order, 1)
