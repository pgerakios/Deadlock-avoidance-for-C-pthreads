#include <pthread.h>
#include <stdlib.h> 
#include <stdio.h>  
#include <unistd.h>

pthread_mutex_t my,mx;
#ifdef FIXED
pthread_mutex_t mg;
#endif

volatile unsigned x, y;
volatile int progress;

#define deposit(x,y,my)                         \
  pthread_mutex_lock(my);                       \
  *y += x;                                      \
  progress = 1;                                 \
  pthread_mutex_unlock(my);

#define withdraw(x,y,my)                        \
  pthread_mutex_lock(my);                       \
  if ( *y >= x ) *y -= x;                       \
  else printf("\nerror withdraw.\n");           \
  progress = 1;                                 \
  pthread_mutex_unlock(my);

#define transfer(x,y,m0,z,m1 ) \
  ({                           \
    int ret = 0;               \
    pthread_mutex_lock(m0);    \
    withdraw(x,y,m0);          \
    deposit(x,z,m1);           \
    ret = *y;                  \
    pthread_mutex_unlock(m0);  \
    ret;                       \
  })

volatile int progress;
volatile unsigned count1=0, count2=0;

void *thread1 (void *p)
{
  int n = (int) p;
  int i;
  for (i=0; i<n; i++) {
#ifndef FIXED
    transfer(1,&y,&my,&x,&mx);
#else
    transfer(1,&y,&mg,&x,&mx);
#endif
    __sync_fetch_and_add(&count1, 1);
#ifdef VERBOSE
    fprintf(stderr,"[%s] = %d\n", "A", z);
#endif
  }
  return 0;
}

void *thread2 (void *p)
{
  int n = (int) p;
  int i;
  for (i=0; i<n; i++) {
#ifndef FIXED
    transfer(1,&x,&mx,&y,&my);
#else
    transfer(1,&x,&mg,&y,&my);
#endif
    __sync_fetch_and_add(&count2, 1);
#ifdef VERBOSE
    fprintf(stderr,"[%s] = %d\n", "B", z);
#endif
  }
  return 0;
}
/* ************************************************************** */

void nsleep (long nsec)
{
  struct timespec sleepTime, remainingSleepTime;
  sleepTime.tv_sec = 0;
  sleepTime.tv_nsec = nsec;
  while (nanosleep(&sleepTime, &remainingSleepTime) != 0)
    sleepTime = remainingSleepTime;
}
#define MONITOR_TIME 100000000 // 0.1 sec

void *monitor (void *p)
{
  while (1) {
    progress = 0;
    nsleep(MONITOR_TIME);
    if (!progress) {
      fprintf(stderr, "deadlock! counts = %u + %u = %u\n",
              count1, count2, count1+count2);
      exit(1);
    }
  }    
}
/* ************************************************************** */
int main (int argc, char *argv[])
{
  if( argc < 3){
    printf("\nExpected initial deposit of x and y.\n");
    exit(-1);
  }
  x = strtoul(argv[1], NULL, 10);
  y = strtoul(argv[2], NULL, 10);
  unsigned sum = x + y;  

  pthread_mutexattr_t at;
  pthread_mutexattr_init(&at);
  pthread_mutexattr_settype(&at,PTHREAD_MUTEX_RECURSIVE_NP);
  pthread_mutex_init(&mx,&at);
  pthread_mutex_init(&my,&at);
#ifdef FIXED
  pthread_mutex_init(&mg,&at);
#endif
  
  pthread_t a, b, m;
  pthread_create(&a, NULL, thread1, (void *) x);
  pthread_create(&b, NULL, thread2, (void *) y);
  pthread_create(&m, NULL, monitor, NULL);
  pthread_join(a, NULL);
  pthread_join(b, NULL);
  printf("Counts = %u + %u = %u\n", count1, count2, count1+count2);
  if (x + y != sum) {
    fprintf(stderr, "sanity violation! %u + %u = %u != %u\n",
            x, y, x+y, sum);
    exit(1);
  }

  return 0; 
}
