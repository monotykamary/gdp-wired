// expect: nonterminating. c is a char: c++ from 127 converts 128 back to char, -128 on every SV-COMP platform (gcc, two's
// complement), so c < 200 holds forever. Over unbounded integers c reaches 200.
int main() {
  char c = 0;
  while (c < 200) {
    c++;
  }
  return 0;
}
