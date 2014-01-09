#include <pthread.h> 

 pthread_mutex_t m0;
 pthread_mutex_t m1;

 int main() {
     pthread_mutex_init(&m0);

     pthread_mutex_lock(&m0);
     pthread_mutex_unlock(&m0);
 }
