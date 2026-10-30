# PREDICTION: refuted; LAW: r.law('n stays zero', ({n}) => n.eq(0))
from typing import Protocol, overload, Literal
class Flags(Protocol):
    @overload
    def value(self, key: Literal['a']) -> int: ...
    @overload
    def value(self, key: str) -> int | None: ...
class Meter:
    def __init__(self, flags: Flags):
        self.flags = flags
        self.n = 0
    def tick(self) -> None:
        self.n = self.flags.value('a')
