#include <stdlib.h>
#include <pthread.h>

pthread_mutex_t * l;

int main ()
{
  l = malloc(sizeof(pthread_mutex_t));
  pthread_mutex_t * l1 = l;
  l = malloc(sizeof(pthread_mutex_t));
  pthread_mutex_t * l2 = l;
  pthread_mutex_lock(l1);
  pthread_mutex_lock(l2);
  pthread_mutex_unlock(l2);
  pthread_mutex_unlock(l1);

  return 0;
}
