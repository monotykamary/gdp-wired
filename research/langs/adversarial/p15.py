# PREDICTION: needs a tag; LAW: r.law('n stays zero', ({n}) => n.eq(0))
from typing import Protocol, TypeVar
T = TypeVar('T')
class Source(Protocol):
    def get_value(self, default: T) -> T: ...
class Meter:
    def __init__(self, source: Source):
        self.source = source
        self.n = 0
    def tick(self) -> None:
        self.n = self.source.get_value(1)
