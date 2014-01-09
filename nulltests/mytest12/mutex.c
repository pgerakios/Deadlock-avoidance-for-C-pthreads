/* *************************************************************
 *
 * This was a bug in the paper version of the tool
 *
 * ************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>

void *functionA();
void *functionB();
void *functionC();
void *functionD();
pthread_mutexattr_t mutexAttribute;
int  counter = 0;

pthread_mutex_t l0;
pthread_mutex_t l1;
pthread_mutex_t l2;
pthread_mutex_t l3;

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
	status = pthread_mutex_init(&l2, &mutexAttribute);
	if (status != 0) { }
	
	
	if( (rc1=pthread_create( &thread1, NULL, &functionC, NULL)) )	{
		printf("Thread creation failed: %d\n", rc1);
	}
	if( (rc2=pthread_create( &thread2, NULL, &functionD, NULL)) )	{
		printf("Thread creation failed: %d\n", rc2);
	}

  usleep(50);
  pthread_create(&m, NULL, monitor, NULL);
  
	pthread_join( thread1, NULL);
  pthread_join( thread2, NULL); 
  exit(0);
}


void *functionC( )
{
  int i = 0;
  pthread_mutex_lock( &l0 );
	usleep(10000);
  while (i++ < 10) {
    pthread_mutex_lock( &l3 );
    pthread_mutex_unlock( &l0 );
	  usleep(10000);
    pthread_mutex_unlock( &l3 );
    progress ++;  
//    printf("C");
    pthread_mutex_lock( &l0 );
  }
  pthread_mutex_unlock( &l0 );
  printf("Thread exiting.\n");
	return (void *) 0;
}


void *functionD( )
{
  int i =0 ;
  pthread_mutex_lock( &l3 );
	usleep(10000);
  while (i++ < 10) {
    pthread_mutex_lock( &l0 );
    pthread_mutex_unlock( &l3 );
	  usleep(10000);
    pthread_mutex_unlock( &l0 );
    progress ++;
//    printf("D");
    pthread_mutex_lock( &l3 );
  }
  pthread_mutex_unlock( &l3 );
  printf("Thread exiting.\n");
	return (void *) 0;
}

void *functionE( )
{
  int i =0 ;
  pthread_mutex_lock( &l3 );
	usleep(10000);
  if (i++ < 10) {
    pthread_mutex_lock( &l0 );
    pthread_mutex_lock( &l3 );
	  usleep(10000);
    pthread_mutex_unlock( &l0 );
    progress ++;
//    printf("D");
    pthread_mutex_unlock( &l3 );
  }
  pthread_mutex_unlock( &l3 );
  printf("Thread exiting.\n");
	return (void *) 0;
}
