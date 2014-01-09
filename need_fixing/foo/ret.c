#include <stdlib.h>
#include <stdio.h>
#include <pthread.h>

struct inner {
  pthread_mutex_t lock;
};

typedef struct {
  pthread_mutex_t *l;
  struct inner * i;
} c_t;

pthread_mutex_t l1;
pthread_mutex_t l2;
pthread_mutex_t arr[10];

void foo(c_t *a, c_t *b) {
 a->l = &l2;
 pthread_mutex_lock(a->l);
 pthread_mutex_lock( & b->i->lock);

 // pthread_mutex_unlock(b->l);
 }


int lock(pthread_mutex_t * l ) {

  return pthread_mutex_lock(l);
}
int unlock(pthread_mutex_t * l ) {

  return pthread_mutex_unlock(l);
}

pthread_mutex_t * global;

int main(int argc, char *argv[]){
 c_t orig;
 orig.l=&l1;
 lock(&l1);
 lock(&l2);
 lock(global);
 pthread_mutex_lock(& arr[3]);
 //foo(&orig,&orig);
 unlock(&l1);
 unlock(&l2);
 return 0;
} 
