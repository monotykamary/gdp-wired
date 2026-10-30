# PREDICTION: refuted; LAW: r.law('n stays zero', ({n}) => n.eq(0))
from typing import Protocol
class Flags(Protocol):
    async def enabled(self) -> bool: ...
class Meter:
    def __init__(self, flags: Flags):
        self.flags = flags
        self.n = 0
    async def tick(self) -> None:
        if await self.flags.enabled():
            self.n = 1
