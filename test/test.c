#include <stdio.h>
#include <stdint.h>
#include <limits.h>

int value = 10;
int * glob1 = &value;
int * glob2 = &value;

void g(int ptr) {
  printf("call to g()\n");
  ptr = ptr ^ ((uintptr_t) glob2);
  *(int *)ptr = 12;
}

int f() {
  int a = 0;
  int * p = &a;
  uintptr_t b = (uintptr_t) p;
  int * q = (int *) b;

  uintptr_t uintglob1 = (uintptr_t) glob1;
  uintptr_t uintp = (uintptr_t) p;
  
  g(uintglob1 ^ uintp);

  if (p==q) { printf("Equal\n"); }
  else { printf("Not Equal\n"); }

  printf("%d\n",a);
  return 0;
}

int main() {
  f();
}

