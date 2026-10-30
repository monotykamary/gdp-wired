# PREDICTION: needs a tag; LAW: r.law('n stays zero', ({n}) => n.eq(0))
from typing import Protocol, Any
class Flags(Protocol):
    def value(self) -> Any: ...
class Meter:
    def __init__(self, flags: Flags):
        self.flags = flags
        self.n = 0
    def tick(self) -> None:
        if self.flags.value():
            self.n = 1
