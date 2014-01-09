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


struct even_deeper {
	int v;
	pthread_mutex_t * deeper;

};

struct deeper {
	int v;
	struct even_deeper * deeper;
	pthread_mutex_t deep;

};

struct inner {
	int v;
	pthread_mutex_t * in_l;
	pthread_mutex_t in_lock;
	struct deeper deep;
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

pthread_mutex_t l1;
pthread_mutex_t l2;

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


	struct even_deeper * even_deeper;
	even_deeper = (struct even_deeper *) malloc(sizeof(struct even_deeper));

	struct inner * inner;
	inner = (struct inner *) malloc(sizeof(struct inner));

	inner->in_l = g1;
	even_deeper->deeper = &l1;
	inner->deep.deeper = even_deeper;
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
	status = pthread_mutex_init(&l1, &mutexAttribute);
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

	exit(0);
}

void doFree (void * p) {
	free(p);
}


void compute(pthread_mutex_t * l) {
	int a[100];

	int i; 
	for ( i = 0 ; i< 100 ; i++)
	{
		pthread_mutex_lock(l);
		a[i] = rand();	
		pthread_mutex_unlock(l);		
	}
	int sum = 0;
	for ( i = 0 ; i< 100 ; i++)
	{
		sum += a[i];
	}
	int m = sum / 100;	

	m++;
	return;

}


void process (struct outer* o, struct outer* o1, int val, struct inner * i, struct even_deeper *ed) {

	pthread_mutex_t * g1;
	pthread_mutex_t * g2;
	g1 = (pthread_mutex_t *) malloc(sizeof(pthread_mutex_t));
	g2 = doMalloc();

	int v1 = 5; 
	int v2 = 9;
	if (v1 % v2 == 0 ) {
		pthread_mutex_lock( & i->deep.deep );
		pthread_mutex_lock( ed->deeper );
	};
	usleep(5000);
	counter++;
	pthread_mutex_lock( i->in_l );
	pthread_mutex_lock( & o->out_lock );

	g1 = & o1->out_lock;
	pthread_mutex_lock( g1 );
	
	//functionB(out);
//	pthread_mutex_t * tmp;
//	tmp = out->out_l;
//	pthread_mutex_lock( tmp );
	compute(& i->in_lock);
	counter++;
	(i->v)++;
	pthread_mutex_lock( & o1->out_lock );

	pthread_mutex_unlock( & o->out_lock );	
	pthread_mutex_unlock( i->in_l );
	pthread_mutex_unlock( ed->deeper );
	pthread_mutex_unlock( & i->deep.deep );
	doFree((void *) g1);
	free((void *) g2);	

}

void *functionA( struct outer * out)
{	

	int i =0;
	if (i>9) {
		pthread_mutex_lock( out->out_l );
		usleep(5000);
		pthread_mutex_lock( & out->out_lock );
		pthread_mutex_lock( (out->in_s)->in_l );

		process(out,out,5,out->in_s, (out->in_s)->deep.deeper);		

		pthread_mutex_unlock( out->out_l );
		pthread_mutex_unlock( & out->out_lock );
		pthread_mutex_unlock( (out->in_s)->in_l );
	}
	else {
		pthread_mutex_lock( out->out_l );
		usleep(5000);
		pthread_mutex_lock( & out->out_lock );
		pthread_mutex_lock( (out->in_s)->in_l );
		if (i<11)
			process(out,out,5,out->in_s, (out->in_s)->deep.deeper);
		/*else 
		{
			pthread_mutex_lock(& out->out_lock);
			pthread_mutex_lock(& out->out_lock);
		}*/

		pthread_mutex_unlock( out->out_l );
		pthread_mutex_unlock( & out->out_lock );
		pthread_mutex_lock( (out->in_s)->in_l );
	}

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

