# PREDICTION: needs a tag; LAW: r.law('n stays zero', ({n}) => n.eq(0))
from typing import Protocol
class Listener(Protocol):
    def emit(self, data: dict[str, int]) -> None: ...
class Meter:
    def __init__(self, listener: Listener):
        self.listener = listener
        self.data: dict[str, int] = {}
        self.n = 0
    def tick(self) -> None:
        self.listener.emit(self.data)
        self.n = self.data.get('n', 0)
