

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include <stddef.h>

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
	int fst; 
	int snd; 
	pthread_mutex_t * a;
	pthread_mutex_t * b;
	int v;
};

void *functionA();
void *functionB();
pthread_mutexattr_t mutexAttribute;


int main()
{
	int rc1, rc2;
	pthread_t thread1, thread2,m;
	printf("Program started\n");

	struct group * g ;
	g = (struct group *) malloc(sizeof(struct group));
	g->a = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));
	g->b = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));

	g->v = 5;
	int * a; 
	a = (int * ) malloc(sizeof(int));


	/* Initialize mutexes and make them reentrant (recursive) */
	int status = pthread_mutexattr_init (&mutexAttribute);
	if (status != 0) { }
	status = pthread_mutexattr_settype(&mutexAttribute,	PTHREAD_MUTEX_RECURSIVE_NP);
	if (status != 0) { }
	status = pthread_mutex_init(g->a, &mutexAttribute);
	if (status != 0) { }
	status = pthread_mutex_init(g->b, &mutexAttribute);
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
  return 0;
}


void *functionA(struct group * g)
{	
  progress = 1;  

  pthread_mutex_t * g1;
	pthread_mutex_t * g2;
	g1 = g->a;
	g2 = g->b;
	int i = 0;

	struct group * h;
	h = g;

	for (i = 0; i < 10000; i++){
	if (g->v % 2 == 0) {
  progress = 1;  

    if(i%100 == 0) fprintf(stderr,"\nTHREAD A: %d",i);		
//		if (g->v % 2 >= 0) {	//	use this to avoid deadlock		
			pthread_mutex_lock( g1 );
			pthread_mutex_lock( g2 );
			pthread_mutex_lock( g2 );			
			g->v ++;
			usleep(10);
			pthread_mutex_unlock( g2 );			
			pthread_mutex_unlock( g2 );
			pthread_mutex_unlock( g1 );		
		}
		else {
			pthread_mutex_lock( h->b );
			pthread_mutex_lock( h->a );
			g->v ++;
			pthread_mutex_unlock( h->a );
			pthread_mutex_unlock( h->b );		
		}
	}
	
	g->v ++;

	return (void *) 0;
}

void *functionB(struct group * g)
{
  progress = 1;  
  
	int i ;
	for (i = 0; i < 10000; i++){
	
    progress = 1;  
    if (g->v % 2 == 0) {
    if(i%100 == 0) fprintf(stderr,"\nTHREAD B: %d",i);		
//		if (g->v % 2 >= 0) {	//	use this to avoid deadlock
			pthread_mutex_lock( g->a );
//		usleep(5000);
			pthread_mutex_lock( g->b );
			g->v ++;
			usleep(10);
			pthread_mutex_unlock( g->b );
			pthread_mutex_unlock( g->a );		
		}
		else {
			pthread_mutex_lock( g->b );
//		usleep(5000);
			pthread_mutex_lock( g->a );
			g->v ++;
			pthread_mutex_unlock( g->a );
			pthread_mutex_unlock( g->b );		
		}
	}
	return (void *) 0;
}



