# PREDICTION: refused; LAW: r.law('n stays zero', ({n}) => n.eq(0))
from typing import Protocol
class Store(Protocol):
    def get(self, key: str) -> int | None: ...
    def set(self, key: str, value: int) -> None: ...
class Meter:
    def __init__(self, a: Store, b: Store):
        self.a = a
        self.b = b
        self.n = 0
    def tick(self) -> None:
        self.a.set('k', 1)
        self.n = self.b.get('k') or 0
