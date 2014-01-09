#include <stdlib.h>
#include <pthread.h>
pthread_mutex_t * l;
pthread_mutex_t  gl;

foo2() {
  l = malloc(sizeof(pthread_mutex_t));
}

foo1() {  
  foo2();
}

bar2() {  
  pthread_mutex_lock(l);
}

bar1() { 
  bar2();
}

work() {
  foo1();
  bar1();  
}

int main () {
  work();
  return 0;
}
