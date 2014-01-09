/* *************************************************************
 *
 * 		Locks malloced in function
 *
 * ************************************************************/


#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>

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
#define MONITOR_TIME 100000000 //0.1 sec

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

void *functionA();
void *functionB();
pthread_mutexattr_t mutexAttribute;
int  counter = 0;
int main()
{
	int rc1, rc2;
	pthread_t thread1, thread2,m;
	printf("Program started\n");

	
	if( (rc1=pthread_create( &thread1, NULL, &functionA, NULL)) )
	{
		printf("Thread creation failed: %d\n", rc1);
	}

	if( (rc2=pthread_create( &thread2, NULL, &functionB, NULL)) )
	{
		printf("Thread creation failed: %d\n", rc2);
	}

  usleep(50);
  pthread_create(&m, NULL, monitor, NULL);

	pthread_join( thread1, NULL);
	pthread_join( thread2, NULL); 

	exit(0);
}


void *functionA()
{	
  progress = 1;  

	pthread_mutex_t * g1;
	pthread_mutex_t * g2;
	g1 = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));
	g2 = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));

	/* Initialize mutexes and make them reentrant (recursive) */
	int status = pthread_mutexattr_init (&mutexAttribute);	if (status != 0) { }
	status = pthread_mutexattr_settype(&mutexAttribute,	PTHREAD_MUTEX_RECURSIVE_NP);	if (status != 0) { }
	status = pthread_mutex_init(g1, &mutexAttribute);	if (status != 0) { }
	status = pthread_mutex_init(g2, &mutexAttribute);	if (status != 0) { }
	
	pthread_mutex_lock( g1 );
	usleep(5000);
	pthread_mutex_lock( g2 );
	counter++;
	printf("Counter value: %d\n",counter);
	pthread_mutex_unlock( g2 );
	pthread_mutex_unlock( g1 );
	return (void *) 0;
}

void *functionB()
{
  progress = 1;  

	pthread_mutex_t * g1;
	pthread_mutex_t * g2;
	pthread_mutex_t * g3;
	g1 = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));
	g2 = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));

	/* Initialize mutexes and make them reentrant (recursive) */
	int status = pthread_mutexattr_init (&mutexAttribute);	if (status != 0) { }
	status = pthread_mutexattr_settype(&mutexAttribute,	PTHREAD_MUTEX_RECURSIVE_NP);	if (status != 0) { }
	status = pthread_mutex_init(g1, &mutexAttribute);	if (status != 0) { }
	status = pthread_mutex_init(g2, &mutexAttribute);	if (status != 0) { }

  int i,j;
  if (j > 10 ) {
    pthread_mutex_lock( g1 );
    if (i > 10 ) {
      pthread_mutex_lock( g2 );
    }
    else if (i > 10) {  
      pthread_mutex_lock( g2 );  
    }
    else {
      pthread_mutex_lock( g2 );
    }
  }



	pthread_mutex_lock( g2 );
	usleep(5000);
	pthread_mutex_lock( g1 );
	counter++;
	printf("Counter value: %d\n",counter);
	pthread_mutex_unlock( g1 );
	pthread_mutex_unlock( g2 );
	return (void *) 0;
}


