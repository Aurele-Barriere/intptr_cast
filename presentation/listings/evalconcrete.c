extern void g();
int f() {
  int a = 0;
  int* q = &a;
  int b = (int) q;
  g();
  return a; }
