# PREDICTION: needs a tag; LAW: r.law('n stays zero', ({n}) => n.eq(0))
module Flags
  def self.enabled; true; end
end
class Meter
  def initialize; @n = 0; end
  def tick
    @n = 1 if Flags.enabled
  end
end
