#include <stdio.h>
#include <stdint.h>
#include <limits.h>

extern void g();

int main() {
  int a = 0;
  int * p = &a;
  int b = (int) p;
  g();
  return b;
}
  
