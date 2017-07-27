extern void g();
int f() {
  int a = 0;
  int* q = &a;
  g();
  return a; }
