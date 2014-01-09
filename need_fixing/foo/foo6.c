#include <stdlib.h>
#include <pthread.h>

pthread_mutex_t * l;
pthread_mutex_t * l1;
pthread_mutex_t * l2;

pthread_mutex_t gl1;
pthread_mutex_t gl2;
pthread_mutex_t gl3;

void * f0 ()
{
  l= &gl2;
}

void * f1 () 
{
  l= &gl2;
  l1 = &gl1;
}

void * f2 () 
{
  l= &gl3;
  f1();
}


int main ()
{
  f0();
  pthread_mutex_lock(l);
  f1();
  pthread_mutex_lock(l);
  f2();
  pthread_mutex_lock(l1);  
  pthread_mutex_unlock(l1);
  f1();
  pthread_mutex_unlock(l);
  f0();
  pthread_mutex_unlock(l);

  return 0;
}
