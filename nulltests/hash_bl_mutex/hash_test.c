#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <assert.h>
#include <time.h>
#include <pthread.h>
#include <sys/time.h>


#include "myhash.h"

/* hash operations */
#define HASH_OPERATIONS 4

//#define DEBUG
#define COUNT

int errno;

#define handle_error_en(en, msg) \
		do { errno = en; perror(msg); exit(EXIT_FAILURE); } while (0)


pthread_barrier_t barr;

#ifdef COUNT
/* Return 1 if the difference is negative, otherwise 0.  */
int timeval_subtract(struct timeval *result, struct timeval *t2, struct timeval *t1) {
  long int diff = (t2->tv_usec + 1000000 * t2->tv_sec) - (t1->tv_usec + 1000000 * t1->tv_sec);
  result->tv_sec = diff / 1000000;
  result->tv_usec = diff % 1000000;
  return (diff<0);
}

#endif


enum {
	HASH_INSERT = 0, /* arg1 = key, arg2 = val     */
	HASH_DELETE,     /* arg1 = key                 */
	HASH_LOOKUP,     /* arg1 = key                 */
	HASH_SWAP,       /* arg1 = key1, arg2 = key2   */
	HASH_LAST,       /* marker */
};

/* hash workload structure */
typedef struct hash_work {
	hash_t        *hash;
	unsigned int  nops; /* number of operations */
} hash_work_t;

/* forward decleration of work function */
//static void do_work(hash_work_t *work);
static void *do_work(void *work_arg);

unsigned long maxkey;


int main(int argc, const char *argv[])
{
  int i;
  int nthreads, nbuckets, nops;
  hash_t *myHash;
  hash_work_t work;


  tmp = (unsigned int)time(NULL);
  srand(tmp);
  
  
  if (argc < 5){
	fprintf(stderr, "Usage: %s <nthreads> <nops> <nbuckets> <maxkey>\n", argv[0]);
	  exit(1);
  }
  nops = atoi(argv[2]);
  nbuckets = atoi(argv[3]);  
  maxkey = atol(argv[4]);

  myHash = hash_init(nbuckets);

  work.hash = myHash;
  work.nops = nops;
  
  /* Initialize lock */
  #ifdef DEBUG
  printf("Main, initialize the lock\n");
  #endif
  rc = pthread_mutex_init(&lock, 0);
  
  
  nthreads = atoi(argv[1]);
  pthread_t* t = (pthread_t *) malloc(nthreads * sizeof(pthread_t));
  int* iret = (int *) malloc(nthreads * sizeof(int));


	/*   initialize affinities */
  
    // Barrier initialization
    if(pthread_barrier_init(&barr, NULL, nthreads))
    {
        printf("Could not create a barrier\n");
        return -1;
    }
    



  /* Create independent threads each of which will execute function */
  int **taskids = (int **) malloc(nthreads * sizeof(int *));  
  for (i = 0; i < nthreads; i++) {
	taskids[i] = (int *) malloc(sizeof(int));
	*taskids[i] = i;
	#ifdef DEBUG
	printf("Creating thread %d\n", i);
	#endif		
	iret[i] = pthread_create( &t[i], NULL, do_work, (void *) &work);  


	/* Set affinity mask to include CPUs 0 */
/*
        CPU_ZERO(&cpuset);
	CPU_SET(i, &cpuset);
	s = pthread_setaffinity_np(t[i], sizeof(cpu_set_t), &cpuset);

	if (s != 0)
		handle_error_en(s, "pthread_setaffinity_np");
*/
  }
  
  /* Wait till threads are complete before main continues. Unless we  */
  /* wait we run the risk of executing an exit which will terminate   */
  /* the process and all threads before the threads have completed.   */
  
  for(i=0;i<nthreads;i++) 
	pthread_join( t[i], NULL);
  

  
  rc = pthread_mutex_destroy(&lock);
    
  for (i=0;i<nthreads; i++) {
	#ifdef DEBUG
	printf("Thread %d returns: %d\n",i,iret[i]);
	#endif
  }
  return 0;
}

static void *do_work(void *work_arg)
{  
  hash_work_t * work = (hash_work_t *) work_arg;
  hash_t *hash;
  unsigned long arg1, arg2;
  unsigned char op;
  unsigned int nops, i;

  hash = work->hash;
  nops = work->nops;

/* Count Time */

  #ifdef COUNT
  struct timeval tvBegin, tvEnd, tvDiff;
  #endif
 #ifdef COUNT
  int rc = pthread_barrier_wait(&barr);
  gettimeofday(&tvBegin, NULL);
  #endif

  for (i = 0; i < nops; i++) {
	  op = 2;//rand() % HASH_OPERATIONS;
	  arg1 = 10 ;//rand_r(&tmp)%maxkey;
	  //printf("Thread %ld rand -> %ld\n", pthread_self(), arg1);

	  switch (op) {
	  case HASH_INSERT:
		  #ifdef DEBUG
		  printf("Thread %ld will now insert.\n", pthread_self());
		  #endif
		  hash_insert(hash, arg1, arg1);
		  break;

	  case HASH_DELETE:
		  #ifdef DEBUG
		  printf("Thread %ld will now delete.\n", pthread_self());
		  #endif
		  hash_delete(hash, arg1);
		  break;

	  case HASH_LOOKUP:
		  #ifdef DEBUG		
		  printf("Thread %ld will now lookup.\n", pthread_self());
		  #endif		  
		  hash_lookup(hash, arg1);
		  break;

	  case HASH_SWAP:
		  #ifdef DEBUG
		  printf("Thread %ld will now swap.\n", pthread_self());
		  #endif
		  arg2 = rand_r(&tmp) % maxkey;
		  hash_swap(hash, arg1, arg2);
		  break;
	  default:
		  fprintf(stderr, "Unknown opcode!\n");
		  assert(0);
	  }

  }
    #ifdef COUNT
  rc = pthread_barrier_wait(&barr);
  gettimeofday(&tvEnd, NULL);
  timeval_subtract(&tvDiff, &tvEnd, &tvBegin);
  printf("time: %ld.%06ld\n", tvDiff.tv_sec, tvDiff.tv_usec);
  #endif  
	//hash_print(hash);
  return(NULL);
}
