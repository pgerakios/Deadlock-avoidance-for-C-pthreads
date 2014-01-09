

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include <stddef.h>
#include <sys/syscall.h>

struct group {
	int counter;
	pthread_mutex_t * guard_v1;
	pthread_mutex_t * guard_v2;	
	pthread_mutex_t * guard_counter;
	int v1;
	int v2;	
};


void *do_work();
pthread_mutexattr_t mutexAttribute;
__thread pid_t thread_pid = -1;

pthread_mutex_t l1;
pthread_mutex_t l3;
pthread_mutex_t l2;

int foo() {return 0;}
pid_t get_tid (int i, int boooomm)
{
  return syscall(SYS_gettid);
}

int main(int argc, const char *argv[])
{
	int i;
	
	int nthreads;
  if (argc < 3){
		fprintf(stderr, "Usage: %s <nthreads> <nops>\n", argv[0]);
	  exit(1);
  }

	printf("Program started\n"); 
  nthreads = atoi(argv[1]);
  pthread_t* t = (pthread_t *) malloc(nthreads * sizeof(pthread_t));
  int* iret = (int *) malloc(nthreads * sizeof(int));  

	struct group * g ;
	g = (struct group *) malloc(sizeof(struct group));
	g->guard_v1 = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));
	g->guard_v2 = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));
	g->guard_counter = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));
	

	g->v1 = 1;
	g->v2 = 2;	
	g->counter = atoi(argv[2]);

	/* Initialize mutexes and make them reentrant (recursive) */
	int status = pthread_mutexattr_init (&mutexAttribute);
	if (status != 0) { }
	status = pthread_mutexattr_settype(&mutexAttribute,	PTHREAD_MUTEX_RECURSIVE_NP);
	if (status != 0) { }
	status = pthread_mutex_init(g->guard_v1, &mutexAttribute);
	if (status != 0) { }
	status = pthread_mutex_init(g->guard_v2, &mutexAttribute);
	if (status != 0) { }
	status = pthread_mutex_init(g->guard_counter, &mutexAttribute);
	if (status != 0) { }

 /* Create independent threads each of which will execute function */
  int **taskids = (int **) malloc(nthreads * sizeof(int *));  
  for (i = 0; i < nthreads; i++) {
		taskids[i] = (int *) malloc(sizeof(int));
		*taskids[i] = i;
		printf("Creating thread %d\n", i);
		iret[i] = pthread_create( &t[i], NULL, do_work, (void *) g);
  }
 
  for(i=0;i<nthreads;i++) 
		pthread_join( t[i], NULL);
  
	exit(0);
}


void * do_work(struct group * g)
{	
	printf("[pid=%u] created\n", (unsigned) thread_pid); 
	pthread_mutex_lock(g->guard_counter);
//	while ((g->counter)-- > 0 ) {

//    thread_pid = get_tid(1,2);
    foo();
//		printf("[pid=%u] ", (unsigned) gthread_pid); 
//		printf("value: %d\n", g->counter);
		pthread_mutex_unlock(g->guard_counter);
		pthread_mutex_lock( g->guard_v1 );
		if (g->v1 % 2 == 0) {	
			g->v1 = rand();
			pthread_mutex_unlock( g->guard_v1 );
		}
		else {
			pthread_mutex_unlock( g->guard_v1 );
			pthread_mutex_lock( g->guard_v2 );
			if (g->v2 % 2 == 0) {	
				g->v2 = rand();
				pthread_mutex_unlock( g->guard_v2 );
			}
			else {
				pthread_mutex_lock( g->guard_v1 );				
				g->v1 = rand();
				pthread_mutex_unlock( g->guard_v1 );				
				g->v2 = rand();				
				pthread_mutex_unlock( g->guard_v2 );							
			}
		}
		pthread_mutex_lock(g->guard_counter);
//	}
	pthread_mutex_unlock(g->guard_counter);
  g->guard_counter = &l1;
  g->guard_counter = &l3;
  g->guard_counter = &l2;  

	printf("[pid=%u] ended\n", (unsigned) get_tid(1,2)); 
	return (void *) 0;
}

