#include <stdlib.h>
#include <pthread.h>

pthread_mutex_t * l;

struct info {
  pthread_mutex_t * a;
  pthread_mutex_t * b;
  pthread_mutex_t c;  
};

pthread_mutex_t gl1;
pthread_mutex_t gl2;
struct info * i;

struct info * doMalloc (struct info * f) {
//  f = (struct info * ) malloc(sizeof(struct info));
  f->a = (pthread_mutex_t *) malloc(sizeof(pthread_mutex_t));
  f->b = (pthread_mutex_t *) malloc(sizeof(pthread_mutex_t));
//  return f;
}

struct info * doMallocB (struct info * f) {
  f->b = (pthread_mutex_t *) malloc(sizeof(pthread_mutex_t));
//  f->b = (pthread_mutex_t *) malloc(sizeof(pthread_mutex_t));
}


int main ()
{

//  struct info * f;
//this should not work  
//  doMalloc1(f);

//this should work  
  i = (struct info * ) malloc(sizeof(struct info));
  doMalloc(i);
//  doMallocB(i);  

  pthread_mutex_lock(i->a);
  pthread_mutex_lock(i->b);
  pthread_mutex_lock( & i->c);
//  pthread_mutex_unlock(i->a);

  return 0;
}
