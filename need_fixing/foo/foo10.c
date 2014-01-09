#include <stdlib.h>
#include <stdio.h>
#include <pthread.h>

pthread_mutex_t * doMalloc () {
  return malloc(sizeof(pthread_mutex_t));
}

hol(pthread_mutex_t ** l1,  pthread_mutex_t ** l2) {
  *l1 = doMalloc();
  *l2 = doMalloc();
}

main () {
  pthread_mutex_t * mainl1;
  pthread_mutex_t * mainl2;
  printf("\n##### in main #####\n\n");
  hol(&mainl1,&mainl2);

  pthread_mutex_lock(mainl1);
  pthread_mutex_unlock(mainl1);

  pthread_mutex_lock(mainl2);
  pthread_mutex_unlock(mainl2);

  printf("\n##### out of main #####\n\n");    
}
