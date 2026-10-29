import threading
import time
from dataclasses import dataclass
from typing import Literal

REFILL_PER_SECOND = 2


class TokenBucket:
    def __init__(self, capacity: int):
        if capacity <= 0:
            raise ValueError("capacity must be positive")
        self.capacity = capacity
        self.tokens = capacity
        self.last: float = time.time()
        self._lock = threading.Lock()

    def take(self, n: int) -> bool:
        if n <= 0:
            raise ValueError("n must be positive")
        with self._lock:
            now = time.time()
            elapsed = now - self.last
            if elapsed > 0:
                self.tokens = min(self.capacity, self.tokens + elapsed * REFILL_PER_SECOND)
                self.last = now
            if self.tokens >= n:
                self.tokens -= n
                return True
            return False


@dataclass
class Budget:
    limit: int
    spent: int = 0


class Ledger:
    def __init__(self) -> None:
        self.budgets: dict[str, Budget] = {}
        self.mode: Literal["open", "closed"] = "open"

    def open_budget(self, user: str, limit: int) -> None:
        if user in self.budgets:
            raise KeyError(user)
        self.budgets[user] = Budget(limit=limit)

    def charge(self, user: str, cost: int) -> bool:
        if self.mode == "closed":
            return False
        b = self.budgets.get(user)
        if b is None or cost < 0:
            return False
        if b.spent + cost > b.limit:
            return False
        b.spent += cost
        return True

    def close(self) -> None:
        self.mode = "closed"


async def check(spend: float, max_budget: float | None) -> None:
    if max_budget is not None and spend >= max_budget:
        raise RuntimeError("over budget")


class SessionLimit:
    """A per-session count in a cache the caller gives (a store): each hit counts one, past the limit refused."""

    def __init__(self, cache, limit: int):
        self.cache = cache
        self.limit = limit

    async def hit(self, session: str) -> None:
        key = f"hits:{session}"
        n = await self.cache.get(key)
        n = (n or 0) + 1
        await self.cache.set(key, n)
        if n > self.limit:
            raise RuntimeError("over the limit")


def drain(xs: dict[str, int]) -> int:
    total = 0
    for k in xs:
        total += xs[k]
    return total
