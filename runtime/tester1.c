#include "hashtable.h"
#include "hashtable_itr.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h> /* for memcmp */
#include <pthread.h>

/*****************************************************************************/
typedef unsigned int uint32_t;

struct path 
{
	char * fun;
	uint32_t line;
	uint32_t byte;
	struct path * next;
};

__thread struct path * path;

struct key
{
    char * gname;
		struct path * path;
};

struct value
{
	pthread_mutex_t * lock_addr;
};


DEFINE_HASHTABLE_INSERT(insert_some, struct key, struct value);
DEFINE_HASHTABLE_SEARCH(search_some, struct key, struct value);
DEFINE_HASHTABLE_REMOVE(remove_some, struct key, struct value);
DEFINE_HASHTABLE_ITERATOR_SEARCH(search_itr_some, struct key);


int path_length(struct path * p);

pthread_mutex_t l1;
pthread_mutex_t l2;

__thread struct hashtable *h;
__thread int count_calls;


/*****************************************************************************
 *
 * 							Hashtable functions
 *
 *
 *
 *****************************************************************************/ 							

static unsigned int
hashfromkey(void *ky) {
    struct key *k = (struct key *)ky;
		struct path *p = k->path;
		unsigned int sum = 0;
		while(p) {
			sum += p->byte;
			p = p->next;		
		}
    return sum;
}

static int
equalkeys(void *k1, void *k2) {
	struct key * key1 = (struct key *) k1;
	struct key * key2 = (struct key *) k2;

	if (0 != strcmp(key1->gname, key2->gname))
		return 0;		
	
	struct path *p1 = key1->path;
	struct path *p2 = key2->path;

	while (p1 && p2) {
		if (0 != strcmp(p1->fun, p2->fun))
			return 0;
		if (p1->byte != p2->byte)
			return 0;
		p1 = p1->next;
		p2 = p2->next;	
	};

	if (((p1==NULL)^(p2==NULL)) == 0) return 0;
	return 1;
}

/*****************************************************************************
 *
 * 									Library functions
 *
 *
 *****************************************************************************/ 									

struct key * create_key (char * name) {
	struct key * k;
	k = (struct key *) malloc(sizeof(struct key));
	k->gname = (char *) malloc(strlen(name));
	strcpy(k->gname, name);
	k->path = path;
	return k;
}

struct value * create_value (pthread_mutex_t * p) {
	struct value * v;
	v = (struct value *) malloc(sizeof(struct value));
	v->lock_addr = p;
	return v;
}

void print_path (struct path * p) {
	struct path * p_itr = p;
	printf("printing path: [");
	while (p_itr) {
		printf("(%s,%d)", p_itr->fun, p_itr->line);
		p_itr = p_itr->next;
	}
	printf("]\n");
}

void insert_in_path (char * fun, uint32_t line, uint32_t byte) {
//	printf("inserting %s ...\n", fun);
	struct path * new_node;
	new_node = (struct path *) malloc(sizeof(struct path));
	new_node->fun = fun;
	new_node->line = line;
	new_node->byte = byte;
	new_node->next = path;
	path = new_node;
	return;
}

/* remove_from_path just moves the global path pointer to the next
 * path node. We keep the whole call graph cause we need the info */
void remove_from_path () {
//	struct path * tbrem;
//	tbrem = path;
	path = path->next;
//	free(tbrem);
}


int path_length(struct path * p) {
	int l = 0;
	struct path * itr;
	itr = p;
	while (itr) { l++; itr = itr->next ; };
	return l;
}

/* create a fresh copy of a path  - the new path will not 
 * be affected by changes int he old one */
struct path * copy_path(struct path * p) {
	struct path * np;
	struct path * nitr;
	struct path * itr;
	struct path * tmp;
	np = NULL;
	nitr = NULL;
	itr = path;
	int i;
	int len = path_length(p);
	for (i = 0 ; i < len ; i++, itr = itr->next) {
		tmp = (struct path*) malloc(sizeof(struct path));
		if (i>0) 
			nitr->next = tmp;
		else
			np = tmp;
		nitr = tmp;
		nitr->fun = (char *) malloc(strlen(itr->fun));
		strcpy(nitr->fun, itr->fun);
		nitr->line = itr->line;
		nitr->byte = itr->byte;
		nitr->next = NULL;
	}
	return np;
}

void print_hash(struct hashtable * h) {
  struct hashtable_itr *itr;
  struct key *k;
	struct value * v;
	int i;
	struct path * p_itr;	
	itr = hashtable_iterator(h);
	i = 0;
	printf("id %lu print hashtable:\n", (unsigned long) pthread_self());
	if (hashtable_count(h) > 0)
	{
		do {
			k = hashtable_iterator_key(itr);
			v = hashtable_iterator_value(itr);
			p_itr = k->path;
			printf("  [");
			while (p_itr) {
				printf("(%s,%d)", p_itr->fun, p_itr->line);
				p_itr = p_itr->next;
			}
			printf("]  --> %ld\n", (long int)v->lock_addr); 

			/* here (kk,v) are a valid (key, value) pair */
			/* We could call 'hashtable_remove(h,kk)' - and this operation
			 * 'free's kk. However, the iterator is then broken.
			 * This is why hashtable_iterator_remove exists - see below.
			 */
			i++;

		} while (hashtable_iterator_advance(itr));
	}
}

//TODO: remove the path nodes when done - 
//might need a list to keep track of them

/*****************************************************************************
 *
 * 												Macros
 *
 *
 *****************************************************************************/ 												


#define init_fun(name, ln, bt, ...)                                    	\
  do {                                                                  \
		if	(count_calls++ == 0) { 																					\
			printf("ID:%lu in %s. Creates new hash.\n",												\
					(unsigned long) pthread_self(), name);												\
			h = create_hashtable(16, hashfromkey, equalkeys); 								\
			if (NULL == h) exit(-1);																					\
			insert_in_path(name, ln, bt); 																		\
		}																																		\
  } while(0)

#define exit_fun(...) 																									\
	do {																																	\
		if	(count_calls-- == 1) {																					\
			remove_from_path();																								\
			print_hash(h);				 																						\
		}																																		\
	} while (0)

#define ins_lock(name, p) 																							\
	do {																																	\
		if (!insert_some(h,create_key(name),create_value(p))) exit(-1);			\
	} while(0)
/*****************************************************************************
 *
 * 												Program
 *
 *
 *****************************************************************************/ 												

pthread_mutex_t * do_malloc () {
	init_fun("do_malloc", 0,0 );
	pthread_mutex_t * p ;

	p = (pthread_mutex_t *) malloc(sizeof(pthread_mutex_t)); 
	ins_lock("&A1",p);

	exit_fun();
	return p;
}

void * bar () {
	init_fun("bar", 0,0 	);
	
	pthread_mutex_t * p;
	insert_in_path("do_malloc", 251, 6600);
	p = do_mall#echo | gcc -E -dM -
RTOBJ=runtime.o hash.o futex.o hashtable.o hashtable_itr.o
ALLOBJ=test.o $(RTOBJ)
TGT=test
LIBS= -lpthread
ARCH=
#$(shell uname -m  | grep "i.*86" |sed 's/^/-march=/')
ARCH64_FLAG=$(shell uname -r | grep 64 | awk '{print "-D__LP64__"}')
DEBUG=-Wall -O3
#DEBUG=-Wall -g
#DEBUG_FLAG=-g -DDEBUG
#DEBUG_FLAG=-g
DEBUG_FLAG=
RT_FLAGS=-D__FUTEX__
#RT_FLAGS=-D__YIELD__
#RT_FLAGS=-D__BUSY__
RT_PERF_COUNTERS=
#RT_PERF_COUNTERS=-D__PERF__COUNTERS__
RT_FUTEX_SPIN_COUNT=-D__FUTEX_SPIN_COUNT__=0
#RT_FUTEX_SPIN_COUNT=-D__FUTEX_SPIN_COUNT__=20
INC=-I/usr/local/lib/ocaml/caml/ -I/usr/lib/ocaml/caml/ -I/usr/lib/ocaml/3.10.2/caml/
CFLAGS= $(RT_FUTEX_SPIN_COUNT) \
	$(RT_PERF_COUNTERS) $(ARCH64_FLAG) $(ARCH) \
	$(RT_FLAGS) -Wall $(DEBUG_FLAG) $(DEBUG) \
	$(INC) -c
#all: $(TGT)

all: $(RTOBJ) 

%.o:	%.c
	$(CC) $(CFLAGS) $< -o $@

$(TGT): $(ALLOBJ) 
	$(CC) $(ALLOBJ) -o $@ $(LIBS) 

clean:
	rm -f *.o

distclean: clean
	rm -f $(TGT)

link: $(RTOBJ) $(EXTOBJ)
	 $(CC) $(RTOBJ) $(EXTOBJ) -o $(EXEC)  $(EXTFLAGS) $(LIBS) 

print_debug_flag:	
	@echo $(DEBUG_FLAG)
c();
	remove_from_path();

	insert_in_path("do_malloc", 255, 6600);
	p = do_malloc();
	remove_from_path();

	exit_fun();

	return (void*) 0;
}

void * foo () {
	init_fun("foo", 0,0 	);

	int i  = 9;
	while (i-- > 0);
	
	insert_in_path("bar", 273, 6600); 
	//this should be here (else we wouldn't know where it was called from)


	bar();	
	remove_from_path();
	
	pthread_t t3;
	pthread_create(&t3, NULL, bar, NULL);  
	pthread_join(t3, NULL);	


/*	insert_in_path("bar", 137, 6600);
	bar();	
	remove_from_path(); */
	exit_fun();
	return (void *) 0;
}


int
main(int argc, char **argv)
{
	init_fun("main",0,0);

  pthread_t t1, t2;

	//insert_in_path("foo", 164, 0);

	pthread_create(&t1, NULL, foo, NULL);  
	pthread_create(&t2, NULL, foo, NULL);  

	pthread_join(t1, NULL);	
	pthread_join(t2, NULL);	

	print_hash(h);
	

	exit_fun();
	/*	struct value *found;
	if (NULL == (found = search_some(h,create_key("&A1")))) {
			printf("BUG: key not found\n");
	} */			
	
	return 0;

}

