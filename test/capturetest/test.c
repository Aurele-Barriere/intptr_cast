#include <stdio.h>
#include <stdint.h>
#include <limits.h>

extern void g();

int f() {
  int a = 0;
  int* q = &a;
  g();
  return a;
}

int main() {
  f();
  return 0;
}
