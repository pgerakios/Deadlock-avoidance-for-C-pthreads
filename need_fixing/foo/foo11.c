#include <stdlib.h>
#include <stdio.h>
#include <pthread.h>

pthread_mutex_t * l;
//pthread_mutex_t * l1;

pthread_mutex_t gl1;
pthread_mutex_t gl2;
struct irrel {
  int i;
};

struct rel {
  int i;
  int j;
  pthread_mutex_t *ptr;
  pthread_mutex_t lock;
};

struct rel j;

bar () {
  printf("\n##### in bar #####\n\n");
  l = malloc(sizeof(pthread_mutex_t));
  printf("\n##### out of bar #####\n\n");  
}

pthread_mutex_t * doMalloc () {
  return malloc(sizeof(pthread_mutex_t));
}

struct rel * r;

foo() {
  int i = 0;
  printf("\n##### in foo #####\n\n");

  r = malloc(sizeof(struct rel));
  bar();
  r->ptr = l;
  printf("\n##### out of foo #####\n\n");  
}

hol(pthread_mutex_t ** l1,  pthread_mutex_t ** l2) {
  int i=10;
  if (i>10) 
    *l1 = doMalloc();
  else
    *l2 = doMalloc();
  *l2 = &gl2;

}

main () {
  pthread_mutex_t * mainl1;
  pthread_mutex_t * mainl2  ;
  printf("\n##### in main #####\n\n");
  foo();
//  mainl2 = & gl2;
  hol(&mainl1,&mainl1);

  pthread_mutex_lock(mainl1);
  pthread_mutex_unlock(mainl1);

//the following give rational error
//  pthread_mutex_lock(mainl2);  
//  pthread_mutex_unlock(mainl2);


  pthread_mutex_lock(r->ptr);
  pthread_mutex_unlock(r->ptr);

  pthread_mutex_lock(& (r->lock));
  pthread_mutex_unlock(& (r->lock));  

  printf("\n##### out of main #####\n\n");    
}
