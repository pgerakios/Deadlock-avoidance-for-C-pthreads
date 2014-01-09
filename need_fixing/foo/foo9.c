#include <stdlib.h>
#include <stdio.h>
#include <pthread.h>

pthread_mutex_t * l;
pthread_mutex_t * l1;

pthread_mutex_t gl;

struct rel {
  int i;
  int j;
  pthread_mutex_t t;
};

struct rel j;

pthread_mutex_t * doMalloc () {
  return malloc(sizeof(pthread_mutex_t));
}


foo() {
  int i = 0;
  printf("\n##### in foo #####\n\n");
  struct rel * r;
  r = malloc(sizeof(struct rel));
  l = & r->t;
  l1 = doMalloc();
  printf("\n##### out of foo #####\n\n");  
}

main () {
  pthread_mutex_t * l2;  
  printf("\n##### in main #####\n\n");
  foo();
  foo();
  l2 = l;

  pthread_mutex_lock(l1);
  pthread_mutex_unlock(l1);
  pthread_mutex_lock(l2);
  pthread_mutex_unlock(l2);  
  printf("\n##### out of main #####\n\n");    
}
