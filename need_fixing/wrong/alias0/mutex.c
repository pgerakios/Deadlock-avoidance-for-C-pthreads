/* *************************************************************
 *
 * 		Locks malloced in main and passed as aguments in a struct
 *
 * ************************************************************/


#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include <stddef.h>

struct group {
	int fst; 
	int snd; 
	pthread_mutex_t * a;
	pthread_mutex_t * b;
	int * v;
};

void *functionA();
void *functionB();
pthread_mutexattr_t mutexAttribute;

int main()
{
	int rc1, rc2;
	pthread_t thread1, thread2;
	printf("Program started\n");

	struct group * g ;
	g = (struct group *) malloc(sizeof(struct group));
	g->a = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));
	g->b = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));
	g->v = (int *) malloc(sizeof(int));
	int tmp = 5;
	g->fst = 7; g->snd = 8;
	g->v = (int *) & tmp;


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

	pthread_join( thread1, NULL);
	pthread_join( thread2, NULL); 

	exit(0);
}


void *functionA(struct group * g)
{	
	pthread_mutex_t * g1;
	pthread_mutex_t * g2;
	g1 = g->a;
	g2 = g->b;
	/*struct group * h1;
	struct group * h2;	
	struct group * h3;	
	h1 = (struct group *) malloc(sizeof(struct group));
	h2 = (struct group *) malloc(sizeof(struct group));	*/
	pthread_mutex_t * aliased;
	int i =9; 
	if (i>10) 
		aliased = g->b;
	else 
		aliased = g->a;

	pthread_mutex_lock( aliased );
	usleep(5000);
	pthread_mutex_lock( g2 );
	g->v ++;
	pthread_mutex_unlock( g2 );
	pthread_mutex_unlock( aliased );
	return (void *) 0;
}

void *functionB(struct group * g)
{

	pthread_mutex_lock( g->b );
	usleep(5000);
	pthread_mutex_lock( g->a );
	g->v ++;
	pthread_mutex_unlock( g->a );
	pthread_mutex_unlock( g->b );
	return (void *) 0;
}



