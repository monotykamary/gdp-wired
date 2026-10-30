# PREDICTION: refuted; LAW: r.law('n stays zero', ({n}) => n.eq(0))
class Meter:
    def __init__(self):
        self.n = 0
    def _write(self) -> None:
        self.n = 1
    def tick(self) -> None:
        self._write()
