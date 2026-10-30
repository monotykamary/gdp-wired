# PREDICTION: refused; LAW: r.law('n stays zero', ({n}) => n.eq(0))
from typing import Protocol
class Source(Protocol):
    def check(self) -> bool: ...
class Meter:
    def __init__(self, source: Source):
        self.source = source
        self.n = 0
    def tick(self) -> None:
        try:
            self.source.check()
        except ValueError:
            self.n = 1
