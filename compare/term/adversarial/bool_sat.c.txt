// expect: nonterminating. b is a _Bool: b + 1 converted back to _Bool is 1 (any nonzero value is 1), so b never
// becomes 2. Over unbounded integers b reaches 2.
int main() {
  _Bool b = 0;
  while (b != 2) {
    b = b + 1;
  }
  return 0;
}
