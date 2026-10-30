# PREDICTION: refused; LAW: r.law('n stays zero', ({n}) => n.eq(0))
from typing import Protocol
from dataclasses import dataclass
@dataclass
class Row:
    n: int = 0
class Repo(Protocol):
    def get(self, key: str) -> Row: ...
class Meter:
    def __init__(self, repo: Repo):
        self.repo = repo
        self.n = 0
    def tick(self) -> None:
        row = self.repo.get('one')
        row.n += 1
        self.n = row.n
