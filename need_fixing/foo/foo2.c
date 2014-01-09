#include <stdlib.h>
#include <pthread.h>

pthread_mutex_t * f ()
{
  return malloc(sizeof(pthread_mutex_t));
}

int main ()
{
  pthread_mutex_t * l1 = f();
  pthread_mutex_t * l2 = f();
  pthread_mutex_lock(l1);
  pthread_mutex_lock(l2);
  pthread_mutex_unlock(l2);
  pthread_mutex_unlock(l1);

  return 0;
}
