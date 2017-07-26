#include <stdio.h>
#include <stdint.h>
#include <limits.h>

extern void g();

int a;

int main() {
  a = 0;
  int b = (int) &a;
  g();
  return b;
}
  
