/* *************************************************************
 *
 *
 * ************************************************************/


#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>

void *functionA();
void *functionB();

pthread_mutex_t l;

struct inner {
	int v;
	pthread_mutex_t * in_l;
	pthread_mutex_t in_lock;
};

struct outer {
	int q;
	pthread_mutex_t * out_l;
	struct inner * in_s;
	pthread_mutex_t out_lock;

};

pthread_mutexattr_t mutexAttribute;
int  counter = 0;

pthread_mutex_t * doMalloc() {
	return (pthread_mutex_t *) malloc(sizeof(pthread_mutex_t));
}

void free_lock(pthread_mutex_t * p) {
	free(p);
}

int main()
{
	int rc1, rc2;
	pthread_t thread1, thread2;
	printf("Program started\n");
	pthread_mutex_t * g1;
	pthread_mutex_t * g2;
	g1 = (pthread_mutex_t *) malloc(sizeof(pthread_mutex_t));
	g2 = (pthread_mutex_t *) malloc(sizeof(pthread_mutex_t));

	struct outer * out;
	out = (struct outer *) malloc(sizeof(struct outer));

	struct inner * inner;
	inner = (struct inner *) malloc(sizeof(struct inner));

	inner->in_l = g1;
	out->out_l = g2;
	out->in_s = inner;

	/* Initialize mutexes and make them reentrant (recursive) */
	int status = pthread_mutexattr_init (&mutexAttribute);
	if (status != 0) { }
	status = pthread_mutexattr_settype(&mutexAttribute,	PTHREAD_MUTEX_RECURSIVE_NP);
	if (status != 0) { }
	status = pthread_mutex_init(g1, &mutexAttribute);
	if (status != 0) { }
	status = pthread_mutex_init(g2, &mutexAttribute);
	if (status != 0) { }

	status = pthread_mutex_init(& out->out_lock, &mutexAttribute);
	if (status != 0) { }

	if( (rc1=pthread_create( &thread1, NULL, &functionA, out)) )
	{
		printf("Thread creation failed: %d\n", rc1);
	}

	if( (rc2=pthread_create( &thread2, NULL, &functionB, out)) )
	{
		printf("Thread creation failed: %d\n", rc2);
	}
	pthread_join( thread1, NULL);
	pthread_join( thread2, NULL); 

	free_lock(g1);
	free_lock(g2);


}


void process (pthread_mutex_t * a, pthread_mutex_t * b) {
	pthread_mutex_lock( a );
	usleep(5000);
	int i = 0; 
	i++;
	pthread_mutex_unlock( a );
	pthread_mutex_lock( b );
	usleep(5000);

	i++;
	pthread_mutex_unlock( b );
}

void *functionA( struct outer * out)
{	

	process(out->in_s->in_l,out->out_l);

	return (void *) 0;
}

void *functionB( struct outer * out)
{	
	pthread_mutex_lock( (out->in_s)->in_l );
	usleep(5000);
	pthread_mutex_lock( out->out_l );

	counter++;
	pthread_mutex_unlock( out->out_l );
	pthread_mutex_unlock( (out->in_s)->in_l );
	return (void *) 0;
}

