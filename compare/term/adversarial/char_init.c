// expect: nonterminating. char c = 300 is 44; the loop runs while c != 300, and a char is never 300.
int main() {
  char c = 300;
  while (c != 300) {
    c = c;
  }
  return 0;
}
