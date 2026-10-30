# PREDICTION: refuted; LAW: r.law('n stays zero', ({n}) => n.eq(0))
from typing import Protocol
class Flags(Protocol):
    def value(self) -> int | None: ...
class Meter:
    def __init__(self, flags: Flags):
        self.flags = flags
        self.n = 0
    def tick(self) -> None:
        value = self.flags.value()
        if value is None:
            self.n = 1
