/* *************************************************************
 *
 * 		Global struct, with function called before lock
 * 		Function pointers
 *
 * ************************************************************/


#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include <sys/syscall.h>

struct group {
	pthread_mutex_t a;
	pthread_mutex_t b;
	int v;
};

struct group * g ;

void functionA();
void functionB();
void * init_fun();

pthread_mutexattr_t mutexAttribute;

pid_t get_tid ()
{
  return syscall(SYS_gettid);
}


int main()
{
	int rc1, rc2;
	pthread_t thread1, thread2;
	printf("Program started\n");

	g = (struct group * )malloc(sizeof(struct group));
	
	/* Initialize mutexes and make them reentrant (recursive) */
	int status = pthread_mutexattr_init (&mutexAttribute);
	if (status != 0) { }
	status = pthread_mutexattr_settype(&mutexAttribute,	PTHREAD_MUTEX_RECURSIVE_NP);
	if (status != 0) { }
	status = pthread_mutex_init(& g->a, &mutexAttribute);
	if (status != 0) { }
	status = pthread_mutex_init(& g->b, &mutexAttribute);
	if (status != 0) { }
	
	if( (rc1=pthread_create( &thread1, NULL, &init_fun, NULL)) )
	{
		printf("Thread creation failed: %d\n", rc1);
	}

	if( (rc2=pthread_create( &thread2, NULL, &init_fun, NULL)) )
	{
		printf("Thread creation failed: %d\n", rc2);
	}

	pthread_join( thread1, NULL);
	pthread_join( thread2, NULL); 

	exit(0);
}



int lock(pthread_mutex_t * l) {
	return pthread_mutex_lock(l);
}

int unlock(pthread_mutex_t * l) {
	return pthread_mutex_unlock(l);
}

void *init_fun() {
	void (* foo)();
	int id = get_tid();
	if (id % 4 == 0) {
		printf("Thread %d: functionA\n", id);
		foo = &functionA;
	}
	else {
		printf("Thread %d: functionB\n", id);		
		foo = &functionB;
	}

	foo();
	return 0;
}


void functionA()
{	
	pthread_mutex_t * k;
	pthread_mutex_t * l;
	k = & g->a;
	l = & g->b; 

	lock( k );
	usleep(5000);
	lock( l );
	g->v ++;
	unlock( l );
	unlock( k );
	return ;
}

void functionB()
{
	pthread_mutex_lock( & g->b );
	usleep(5000);
	pthread_mutex_lock( & g->a );
	g->v ++;
	pthread_mutex_unlock( & g->a );
	pthread_mutex_unlock( & g->b );
	return;
}




