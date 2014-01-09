#include <pthread.h> 

 pthread_mutex_t m0;
 pthread_mutex_t m1;

 void *thread(void *dummy) {
   pthread_mutex_lock(&m1);
   pthread_mutex_unlock(&m1);
 }

 int main(int argc, char *argv[]) {
       pthread_mutex_init(&m0);
       pthread_mutex_init(&m1);
       pthread_t tid;
       pthread_create(&tid,0,thread,0);
       pthread_mutex_lock(&m0);
       pthread_mutex_lock(&m1);
       pthread_mutex_unlock(&m1);
       pthread_mutex_unlock(&m0);    
 }
