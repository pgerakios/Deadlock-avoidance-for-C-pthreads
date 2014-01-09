/* *************************************************************
 *   Pro test1:
 *
 *   Malloc in some init function.
 *   Lock/Unlock wrappers.	
 *
 * ************************************************************/


#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <unistd.h>

struct group {
	int fst; 
	int snd; 
	pthread_mutex_t * a;
	pthread_mutex_t * b;
	int * v;
};

void *functionA();
void *functionB();

struct group *malloc_g() {
   struct group *g;
	g = (struct group *) malloc(sizeof(struct group));
	g->a = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));
	g->b = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));
	g->v = (int *) malloc(sizeof(int));
	g->fst = 7; g->snd = 8;
	g->v = (int *) malloc(sizeof(int));
	/* Initialize mutexes and make them reentrant (recursive) */
        pthread_mutexattr_t mutexAttribute;
	int status = pthread_mutexattr_init (&mutexAttribute);
	if (status != 0) { }
	status = pthread_mutexattr_settype(&mutexAttribute,	PTHREAD_MUTEX_RECURSIVE_NP);
	if (status != 0) { }
	status = pthread_mutex_init(g->a, &mutexAttribute);
	if (status != 0) { }
	status = pthread_mutex_init(g->b, &mutexAttribute);
	if (status != 0) { }
        pthread_mutexattr_destroy (&mutexAttribute);
        return g;
}

void free_g(struct group* g) {
   free(g);
}
void lock_a(struct group* g) {
	pthread_mutex_lock( g->a );
}
void unlock_a(struct group * g) {
	pthread_mutex_unlock( g->a );
}
void lock_b(struct group* g) {
	pthread_mutex_lock( g->b );
}
void unlock_b(struct group * g) {
	pthread_mutex_unlock( g->b );
}

pthread_t tids[10000];
int THREADS = 10;
int main()
{
	int i;

	struct group * g = malloc_g();
        printf("Program started\n");
        for(i=0;i<THREADS;i++)
	if(pthread_create(tids+i, NULL, &functionA, g))
		perror("Thread creation failed.\n");
        for(i=0;i<THREADS;i++)
           pthread_join(tids[i], NULL);
        free(g);
        return 0;
}

__thread int iterations = 5000;
void *functionA(struct group * g)
{	
  struct group * h = g;
  fprintf(stderr,"\nThread %p started.",&g);
  while(iterations--){               
        lock_a(h);
        usleep(random() % 50);
        lock_b(g);
	g->v ++;
        usleep(random() % 50);
        unlock_b(g);
        usleep(random() % 50);
        unlock_a(h);
   }
  fprintf(stderr,"\nThread %p done.",&g);
	return (void *) 0;
}
