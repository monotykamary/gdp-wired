# PREDICTION: needs a tag; LAW: r.law('n stays zero', ({n}) => n.eq(0))
from typing import Protocol
class Listener(Protocol):
    def emit(self, x: object) -> None: ...
class Meter:
    def __init__(self, listener: Listener):
        self.listener = listener
        self.n = 0
    def tick(self) -> None:
        alias = self
        self.listener.emit(alias)
