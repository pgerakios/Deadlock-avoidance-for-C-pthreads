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


struct group {
	pthread_mutex_t * a;
	pthread_mutex_t * b;
	int v;
};

pthread_mutex_t l1;
pthread_mutex_t l2;
#define BRIGHT 1
#define RED 31
#define BG_BLACK 40

void *functionA();
void *functionB();
pthread_mutexattr_t mutexAttribute;
int  counter = 0;
int main()
{
	int rc1;
	pthread_t thread1,m;
	printf("Program started\n");

	
	if( (rc1=pthread_create( &thread1, NULL, &functionA, NULL)) )
	{
		printf("Thread creation failed: %d\n", rc1);
	}
  
  usleep(50);
  pthread_create(&m, NULL, monitor, NULL);

	pthread_join( thread1, NULL);


	exit(0);
}

void lock_wrap (pthread_mutex_t * p) {
	pthread_mutex_lock(p);
	return;
}

void struct_lock_wrap (struct group * s) {
	pthread_mutex_lock(s->a);
	pthread_mutex_lock(s->b);
	return;
}

void struct_unlock_wrap (struct group * s) {
	pthread_mutex_unlock(s->a);
	pthread_mutex_unlock(s->b);
	return;
}

void *functionA()
{	
	int rc2;
	pthread_t thread2;
  progress = 1;  
	printf("Running funcitonA.\n");
	struct group * g ;
	g = (struct group *) malloc(sizeof(struct group));
	g->a = &l1;
	g->b = &l2;

	struct group * h ;
	h = (struct group *) malloc(sizeof(struct group));
	h->a = &l1;
	h->b = &l2;

	/* Initialize mutexes and make them reentrant (recursive) */
	int status = pthread_mutexattr_init (&mutexAttribute);
	if (status != 0) { }
	status = pthread_mutexattr_settype(&mutexAttribute,	PTHREAD_MUTEX_RECURSIVE_NP);
	if (status != 0) { }
	status = pthread_mutex_init(g->a, &mutexAttribute);
	if (status != 0) { }
	status = pthread_mutex_init(g->b, &mutexAttribute);
	if (status != 0) { }
	
	if( (rc2=pthread_create( &thread2, NULL, &functionB, h)) ) {
		printf("Thread creation failed: %d\n", rc2);
	}

	lock_wrap( g->a );
	usleep(5000);

	struct_lock_wrap( g );
	counter++;
	printf("Counter value: %d\n",counter);	
	struct_unlock_wrap( g );

	pthread_mutex_unlock( g->a );


	pthread_join( thread2, NULL); 
	return (void *) 0;
}

void *functionB(struct group * g)
{	
  progress = 1;  
	printf("Running funcitonB.\n");
	pthread_mutex_lock( g->b );
	usleep(5000);
	pthread_mutex_lock( g->a );
	counter++;
	printf("Counter value: %d\n",counter);
	pthread_mutex_unlock( g->a );
	pthread_mutex_unlock( g->b );
	return (void *) 0;
}


