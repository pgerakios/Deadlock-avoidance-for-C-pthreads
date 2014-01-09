/* *************************************************************
 *
 * 	Simple case of global locks
 *
 * ************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>

void *functionA();
void *functionB();
pthread_mutexattr_t mutexAttribute;
int  counter = 0;

pthread_mutex_t l1;
pthread_mutex_t l2;
pthread_mutex_t l3;
pthread_mutex_t l4;
pthread_mutex_t l5;
pthread_mutex_t l6;


volatile int progress;

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
      fprintf(stderr, "deadlock!");
      exit(1);
    }
  }    
}

int main()
{
	int rc1, rc2;
	pthread_t thread1, thread2, m;
	printf("Program started\n");

	int status = pthread_mutexattr_init (&mutexAttribute);
	if (status != 0) { }
	status = pthread_mutexattr_settype(&mutexAttribute,	PTHREAD_MUTEX_RECURSIVE_NP);
	if (status != 0) { }
	status = pthread_mutex_init(&l1, &mutexAttribute);
	if (status != 0) { }
	status = pthread_mutex_init(&l2, &mutexAttribute);
	if (status != 0) { }
	status = pthread_mutex_init(&l3, &mutexAttribute);
	if (status != 0) { }
	status = pthread_mutex_init(&l4, &mutexAttribute);
	if (status != 0) { }
	status = pthread_mutex_init(&l5, &mutexAttribute);
	if (status != 0) { }
	status = pthread_mutex_init(&l6, &mutexAttribute);
	if (status != 0) { }
	
	
  pthread_create(&m, NULL, monitor, NULL);
	
  if( (rc1=pthread_create( &thread1, NULL, &functionA, NULL)) )	{
		printf("Thread creation failed: %d\n", rc1);
	}

	if( (rc2=pthread_create( &thread2, NULL, &functionB, NULL)) )	{
		printf("Thread creation failed: %d\n", rc2);
	}

  usleep(50);
  
	pthread_join( thread1, NULL);
	pthread_join( thread2, NULL); 
  exit(0);
}


void *functionA( )
{
  progress = 1;  

  pthread_mutex_lock( &l1 );
  usleep(50);
  pthread_mutex_lock( &l2 );
  pthread_mutex_lock( &l3 );
  pthread_mutex_lock( &l4 );
  pthread_mutex_lock( &l5 );
  pthread_mutex_lock( &l6 );
  pthread_mutex_unlock( &l6 );
  pthread_mutex_unlock( &l5 );
  pthread_mutex_unlock( &l4 );
  pthread_mutex_unlock( &l3 );
  pthread_mutex_unlock( &l2 );
  pthread_mutex_unlock( &l1 );
  printf("Thread exiting.\n");
  return (void *) 0;
}

  
void *functionB( )
{
  progress = 1;  
	pthread_mutex_lock( &l2 );
	usleep(50);
	pthread_mutex_lock( &l1 );
	counter++;
	pthread_mutex_unlock( &l1 );
	pthread_mutex_unlock( &l2 );
  printf("Thread exiting.\n");
	return (void *) 0;
}

