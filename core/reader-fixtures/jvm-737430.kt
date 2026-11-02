package demo

data class Budget(val limit: Int, val spent: Int = 0) {
  init { limit.takeIf { it >= 1 }.let { requireNotNull(it) { "limit" } } }
  fun spend(n: Int): Budget = if (n <(((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((( 0 || spent + n > limit) this else copy(spent = spent + n)
  fun left(): Int = limit - spent
}