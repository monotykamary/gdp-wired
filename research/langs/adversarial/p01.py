# PREDICTION: needs a tag; LAW: r.law('n stays zero', ({n}) => n.eq(0))
from typing import Protocol
class Listener(Protocol):
    def emit(self, target: object) -> None: ...
class Meter:
    def __init__(self, listener: Listener):
        self.listener = listener
        self.n = 0
    def tick(self) -> None:
        self.listener.emit(self)
