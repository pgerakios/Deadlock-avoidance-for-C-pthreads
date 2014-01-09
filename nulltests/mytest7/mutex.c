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



struct inner {
	int i;
	pthread_mutex_t in_l;

};
struct group {
	struct inner inner;
	pthread_mutex_t a;
	pthread_mutex_t b;
	int v;
};

struct small {
	pthread_mutex_t * a;
	pthread_mutex_t * b;
};

struct group * g ;

void *functionA();
void *functionB();
pthread_mutexattr_t mutexAttribute;

int main()
{
	int rc1;
	pthread_t thread1,m;
	printf("Program started\n");

	g = (struct group * )malloc(sizeof(struct group));
	g->v = 0;
	if( (rc1=pthread_create( &thread1, NULL, &functionA, NULL)) )
	{
		printf("Thread creation failed: %d\n", rc1);
	}
  usleep(50);
  pthread_create(&m, NULL, monitor, NULL);
 
	pthread_join( thread1, NULL);
	exit(0);
}


void *functionA()
{	
	pthread_t thread2;
	struct group * a;
  int rc;
  a = (struct group *) malloc(sizeof(struct group));
  /* Initialize mutexes and make them reentrant (recursive) */
  pthread_mutexattr_init (&mutexAttribute);
  pthread_mutexattr_settype(&mutexAttribute,	PTHREAD_MUTEX_RECURSIVE_NP);
  pthread_mutex_init(& a->a , &mutexAttribute);
  pthread_mutex_init(& a->b , &mutexAttribute);  
  pthread_mutex_init(& (a->inner).in_l , &mutexAttribute);

  struct small * s;
  s = (struct small *) malloc(sizeof(struct small));
  s->a = & a->a ;
  s->b = & (a->inner).in_l;

	while (g->v < 2 ) {
    progress = 1;  	

		if(( rc = pthread_create( &thread2, NULL, &functionB, s))) {
			printf("Thread creation failed: %d\n", rc);
		}

		pthread_mutex_lock( & a->a );
		usleep(5000);
		pthread_mutex_lock( & (a->inner).in_l );
		printf ("FuntionA: %d\n", g->v);
		g->v ++;
		pthread_mutex_unlock( & (a->inner).in_l );		
		pthread_mutex_unlock( & a->a );

		pthread_join( thread2, NULL);


	}
  free(a);
  return (void *) 0;
}

void *functionB(struct small * g)
{
	int i ; 
	for (i = 0 ; i < 1 ; i++) {
    progress = 1;  	    
		pthread_mutex_lock( g->b );
		usleep(5000);
		pthread_mutex_lock( g->a );
		printf ("FunctionB: %d\n" , i );

		pthread_mutex_unlock( g->a );
		pthread_mutex_unlock( g->b );
	}
	return (void *) 0;
}




