/* *************************************************************
 *
 * 		Locks malloced in function
 *
 * ************************************************************/


#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>

void *functionA();
void *functionB();
pthread_mutexattr_t mutexAttribute;
pthread_mutex_t l;

/* ************************************************************** */
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
/* ************************************************************** */


int main()
{
	int rc1, rc2;
	pthread_t thread1, thread2,m;
	printf("Program started\n");
	pthread_mutex_t * g;
	g = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));

	/* Initialize mutexes and make them reentrant (recursive) */
	int status = pthread_mutexattr_init (&mutexAttribute);	if (status != 0) { }
	status = pthread_mutexattr_settype(&mutexAttribute,	PTHREAD_MUTEX_RECURSIVE_NP);
	if (status != 0) { }
	status = pthread_mutex_init(g, &mutexAttribute);
	if (status != 0) { }
	status = pthread_mutex_init( &l, &mutexAttribute);
	if (status != 0) { }

	if( (rc1=pthread_create( &thread1, NULL, &functionA, g)) )
	{
		printf("Thread creation failed: %d\n", rc1);
	}

	if( (rc2=pthread_create( &thread2, NULL, &functionB, g)) )
	{
		printf("Thread creation failed: %d\n", rc2);
	}
  
  usleep(50);
  pthread_create(&m, NULL, monitor, NULL);
 
	pthread_join( thread1, NULL);
	pthread_join( thread2, NULL); 

	exit(0);
}
/*
void lock_wrap( pthread_mutex_t p) {
	pthread_mutex_lock( &p );
	return;
}
*/
void *functionA(pthread_mutex_t * g)
{	
  progress = 1;  	
	pthread_mutex_lock( g );
	usleep(5000);
	pthread_mutex_lock( &l );

	pthread_mutex_unlock( &l );
	pthread_mutex_unlock( g );
	return (void *) 0;
}

void *functionB(pthread_mutex_t * g)
{
  progress = 1;  
	pthread_mutex_lock( &l );
	usleep(5000);
	pthread_mutex_lock( g );
	
	pthread_mutex_unlock( g );
	pthread_mutex_unlock( &l );
	return (void *) 0;
}




