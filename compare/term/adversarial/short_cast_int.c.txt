// expect: nonterminating. (short) 40000 is -25536 (two's complement), stored in an int: s stays below 30000 and the
// loop goes on; a cast read as the identity would leave s at 40000 and end it.
int main() {
  int x = 40000;
  int s = 0;
  while (s < 30000) {
    s = (short) x;
  }
  return 0;
}
