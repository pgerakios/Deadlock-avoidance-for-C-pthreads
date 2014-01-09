#include <stdlib.h>
#include <stdio.h>
#include <pthread.h>

pthread_mutex_t * l;
pthread_mutex_t * l1;
pthread_mutex_t * l2;


pthread_mutex_t gl;

struct rel {
  int i;
  int j;
  pthread_mutex_t t;
  struct inner * in;
};

struct inner {
  int i;
  int j;
  pthread_mutex_t a;
  pthread_mutex_t *ptr;
};



struct rel j;

pthread_mutex_t * doMalloc () {
  printf("\n##### in doMalloc #####\n\n");
  pthread_mutex_t * local;
  pthread_mutexattr_t mutexAttribute;  
  local = malloc(sizeof(pthread_mutex_t)) ;
	int status = pthread_mutexattr_init (&mutexAttribute);
	if (status != 0) { }
	status = pthread_mutexattr_settype(&mutexAttribute,	PTHREAD_MUTEX_RECURSIVE_NP);
	if (status != 0) { }
	status = pthread_mutex_init(local, &mutexAttribute);
	if (status != 0) { }  
  printf("\n##### out of doMalloc #####\n\n");
  return local;

}

struct rel  * globrel;

foo(pthread_mutex_t ** l0) {
  int i = 0;
  printf("\n##### in foo #####\n\n");
  
  struct rel * r;
  r = globrel;
  r = malloc(sizeof(struct rel));

  r->in = malloc(sizeof(struct inner));
  r->in->ptr = doMalloc();
  *l0 = & r->t;
  printf("\n##### out of foo #####\n\n");  

}




main () {
  printf("\n##### in main #####\n\n");
  foo(&l1);
  foo(&l2);


  pthread_mutex_lock(l1);
  pthread_mutex_lock(l2);
  pthread_mutex_unlock(l2);  
  pthread_mutex_unlock(l1);

  printf("\n##### out of main #####\n\n");    
}
