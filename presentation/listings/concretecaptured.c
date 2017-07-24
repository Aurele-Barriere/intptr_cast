extern void g();
int f(void) {
  int a = 0;
  capture(&a);
  int p = (int) &a;
  g();
  return a+p;
}
