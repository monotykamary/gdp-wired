# PREDICTION: refused; LAW: r.law('n stays zero', ({n}) => n.eq(0))
value = 0
def bump() -> None:
    global value
    value = 1
class Meter:
    def __init__(self):
        self.n = 0
    def tick(self) -> None:
        bump()
        self.n = value
