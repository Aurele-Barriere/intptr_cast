extern void g();
int f(void) {
  int a = 0;
  int p = (int) &a;
  g();
  return a+p;
}
