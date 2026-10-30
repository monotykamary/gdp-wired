# PREDICTION: needs a tag; LAW: r.law('n stays zero', ({n}) => n.eq(0))
from typing import Protocol
from dataclasses import dataclass
@dataclass
class Row:
    n: int = 0
class Repo(Protocol):
    def save(self, key: str, row: Row) -> None: ...
class Meter:
    def __init__(self, repo: Repo):
        self.repo = repo
        self.row = Row()
        self.n = 0
    def tick(self) -> None:
        self.repo.save('one', self.row)
        self.n = self.row.n
