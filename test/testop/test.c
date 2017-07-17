#include<stdio.h>
#include<stdlib.h>


void g() {
  int b = 0;
}

int f() {
  int a = 0;

  g();
  return a;
}

int main() {
  f();
}
