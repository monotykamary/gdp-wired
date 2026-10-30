# PREDICTION: refused; LAW: r.law('n stays zero', ({n}) => n.eq(0))
from typing import Protocol
class Flags(Protocol):
    def enabled(self) -> bool: ...
class Meter:
    flags: Flags
    def __init__(self):
        self.n = 0
    def tick(self) -> None:
        if self.flags.enabled():
            self.n = 1
