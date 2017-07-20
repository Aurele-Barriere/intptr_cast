int main() {
  int a = 0;
  int * p = &a;
  int b = (int) p;
  int * q = (int *) (b+2);
  return 0;
}
