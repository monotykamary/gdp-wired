# PREDICTION: refuted; LAW: r.law('n stays zero', ({n}) => n.eq(0))
from typing import Protocol
from fastapi import Depends
class Cache(Protocol):
    def get(self, key: str) -> int | None: ...
    def set(self, key: str, value: int) -> None: ...
class InMemory:
    def __init__(self): self.data = {}
    def get(self, key: str) -> int | None: return self.data.get(key)
    def set(self, key: str, value: int) -> None: self.data[key] = value
def get_cache():
    cache = InMemory()
    try:
        yield cache
    finally:
        cache.data.clear()
class Meter:
    def __init__(self, cache: Cache = Depends(get_cache)):
        self.cache = cache
        self.n = 0
    def tick(self) -> None:
        self.cache.set('k', 1)
        self.n = self.cache.get('k') or 0
