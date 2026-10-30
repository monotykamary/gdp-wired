# PREDICTION: needs a tag; LAW: r.law('n stays zero', ({n}) => n.eq(0))
class Meter
  def initialize(listener)
    @listener = listener
    @n = 0
  end
  def tick
    @listener.emit(self)
  end
end
