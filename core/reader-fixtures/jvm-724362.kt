package demo

data class Budget(val limit: Int, val spent: Int = 0) {
  init { limit.takeIf { it >= 0 }.let { requireNotNull(it) { "limit" } } }
  fun spend(n: Int): Budget = if (n < 0 || spent + n > limit)  else copy(spent = spent + n)
  fun reset(): Budget = copy(spent = 0)
  fun left(): Int = limit - spent
}