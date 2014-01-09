/* *************************************************************
 *
 * 		Casting Issues (paramenter void is casted in program)
 *
 * ************************************************************/


#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include <sys/syscall.h>
#define N 50
#define THREADS 4


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


void *functionA();
void *functionB();

struct inner {
	pthread_mutex_t * ina;
	pthread_mutex_t * inb;	
}
;

struct info {
	int ** a;
	int ** b;
	int ** c;	
	pthread_mutex_t * la;
	pthread_mutex_t * lb;	
  struct inner * inner;
}
;

struct info1 {
  struct inner * inner;
}
;

pid_t get_tid ()
{
  return syscall(SYS_gettid);
}


pthread_mutex_t l;

pthread_mutexattr_t mutexAttribute;
int  counter = 0;
int main()
{
	int rc1;
	pthread_t thread1,m;
	
	if( (rc1=pthread_create( &thread1, NULL, &functionA, NULL)) )
	{printf("Thread creation failed: %d\n", rc1);}
//	if( (rc2=pthread_create( &thread2, NULL, &functionB, NULL)) )
//	{printf("Thread creation failed: %d\n", rc2);}

  usleep(50);
  pthread_create(&m, NULL, monitor, NULL);

  functionA();



	pthread_join( thread1, NULL);
//	pthread_join( thread2, NULL); 

	exit(0);
}

pthread_mutex_t * doMalloc() {
	return (pthread_mutex_t *) malloc(sizeof(pthread_mutex_t));
}

void locka(pthread_mutex_t * a, pthread_mutex_t * b) {
	pthread_mutex_lock(a);
	return;
}

void lockb(pthread_mutex_t * a, pthread_mutex_t * b) {
	pthread_mutex_lock(b);
	return;
}

void unlocka(pthread_mutex_t * a, pthread_mutex_t * b) {
	pthread_mutex_unlock(a);
	return;
}

void real_unlockb(pthread_mutex_t * a, pthread_mutex_t * b) {
	pthread_mutex_unlock(b);
	return;
}

void unlockb(pthread_mutex_t * ua, pthread_mutex_t * ub) {
  real_unlockb(ua,ub);
	return;
}


void *computation( void * in ) {
	int i, j , k, s ; 
	struct info * str = (struct info *) in;

	int ** a = str->a;
	int ** b = str->b;		
	int ** c = str->c;			
	for (i = 0 ; i < N; i++) {
			for (j = 0 ; j < N; j++) {
				locka(str->la, str->lb);
				s = 0;
				for (k = 0 ; k < N; k++) {
          progress = 1;            
					lockb( str->la, str->lb);
					s += a[i][k]*b[k][j];
					unlockb(str->la, str->lb);
				}
        
				c[i][j] = s;
				unlocka(str->la, str->lb);
			}
	}
	return (void *) 0;
}

pthread_mutex_t g;

void *functionA()
{	
  progress = 1;  

	struct info * str1;
	str1 = (struct info * ) malloc(sizeof(struct info));

	str1->la = doMalloc();
	str1->lb = doMalloc();
  str1->inner = (struct inner *) malloc(sizeof(struct inner));
//  pthread_mutex_lock(&g);
  str1->inner->ina = doMalloc();
  str1->inner->inb = doMalloc();

	int i;
	str1->a = (int ** ) malloc(N * sizeof(int *));
	str1->b = (int ** ) malloc(N * sizeof(int *));
	str1->c = (int ** ) malloc(N * sizeof(int *));		


	for (i =0 ; i < N; i++ ) {
    progress = 1;  
    
		str1->a[i] = (int *) malloc(N * sizeof(int));
		str1->b[i] = (int *) malloc(N * sizeof(int));
		str1->c[i] = (int *) malloc(N * sizeof(int));			
	}

	struct info * str2;
	str2 = (struct info * ) malloc(sizeof(struct info));
	str2->la = str1->lb;
	str2->lb = str1->la;
   str2->inner = str1->inner;

	str2->a = (int ** ) malloc(N * sizeof(int *));
	str2->b = (int ** ) malloc(N * sizeof(int *));
	str2->c = (int ** ) malloc(N * sizeof(int *));		

	for (i =0 ; i < N; i++ ) {
    progress = 1;  
	
    str2->a[i] = (int *) malloc(N * sizeof(int));
		str2->b[i] = (int *) malloc(N * sizeof(int));
		str2->c[i] = (int *) malloc(N * sizeof(int));			
	}

	printf("[%d] Alloced arrays.\n", 
      get_tid());	
	

	pthread_mutexattr_init (&mutexAttribute);
	pthread_mutexattr_settype(&mutexAttribute,	PTHREAD_MUTEX_RECURSIVE_NP);
	pthread_mutex_init(str1->la, &mutexAttribute);
	pthread_mutex_init(str1->lb, &mutexAttribute);
	pthread_mutex_init(str2->la, &mutexAttribute);
	pthread_mutex_init(str2->lb, &mutexAttribute);
		

	int rc;
	pthread_t thr[THREADS];

	for (i = 0 ; i < THREADS ; i++ ){
    progress = 1;  
    
		printf("[%d] Creating thread.\n", get_tid());
		if (i % 2 ==0) {
			if( (rc = pthread_create( &thr[i], NULL, &computation, (void *) str1 )) )
			{printf("Thread creation failed: %d\n", rc);}		
		}
		else
			if( (rc = pthread_create( &thr[i], NULL, &computation, (void *) str2 )) )
			{printf("Thread creation failed: %d\n", rc);}			
	}


	for (i = 0 ; i < THREADS ; i++ ){
		pthread_join(thr[i], NULL);
	};

	return (void *) 0;
}

void *functionB()
{
  progress = 1;  

	pthread_mutex_t * g1;
	pthread_mutex_t * g2;
	g1 = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));
	g2 = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));
	/* Initialize mutexes and make them reentrant (recursive) */
	int status = pthread_mutexattr_init (&mutexAttribute);
	if (status != 0) { }
	status = pthread_mutexattr_settype(&mutexAttribute,	PTHREAD_MUTEX_RECURSIVE_NP);
	if (status != 0) { }
	status = pthread_mutex_init(g1, &mutexAttribute);
	if (status != 0) { }
	status = pthread_mutex_init(g2, &mutexAttribute);
	if (status != 0) { }

	pthread_mutex_lock( g2 );
	usleep(5000);
	pthread_mutex_lock( g1 );
	counter++;
	printf("Counter value: %d\n",counter);
	pthread_mutex_unlock( g1 );
	pthread_mutex_unlock( g2 );
	return (void *) 0;
}


