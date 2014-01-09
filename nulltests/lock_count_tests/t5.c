#include <pthread.h> 

 pthread_mutex_t m0;
 pthread_mutex_t m1;

 void unlock(pthread_mutex_t *m){
  pthread_mutex_unlock(m);    
 }
 int main(int argc, char *argv[]) {
     pthread_mutex_init(&m0);
     pthread_mutex_init(&m1);
     pthread_mutex_lock(&m0);
     pthread_mutex_lock(&m1);
     unlock(&m0);    
     pthread_mutex_unlock(&m1);
 }
