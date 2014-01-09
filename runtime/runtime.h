/* Authors: Prodromos Gerakios and Nikolaos Papaspyrou
 *
 * All rights reserved.
 */
#ifndef __RUNTIME_H__
#define __RUNTIME_H__
#include <pthread.h> 

#include "hashtable.h"
#include "hashtable_itr.h"
//#define DEBUG

// SEQ is useless but it cannot be removed
typedef struct meta_info {

  enum {
    SIMPLE  =  0,
    PATH    =  1,
    CALL    = -1,
    SEQ     = -2
  } tag : 2;

  enum {
    LOCK    =  1,
    UNLOCK  = -1
  } type : 2;                    // VALID only when tag = SIMPLE
  
  enum {
    STACK             = -3,
    HEAP              = -2,
    GLOBAL_DRF_HDL    = -1,
    GLOBAL_NODRF_HDL  =  0,
    GLOBAL_DRF_PTR    =  1,
    GLOBAL_NODRF_PTR  =  2
  } mem : 4;                                          // VALID only when tag = SIMPLE

  unsigned char has_parent  : 1;                        // true is thee exists a parent node 
  unsigned char dummy       : 1;
  unsigned int parent;                                // WARNING: PV: changed these to support larger effect arrays
                                                      // parent must be allocated before children (unsigned char)
  unsigned int parent_offset;                         // offset within parent array
  unsigned int size;                                  // If TAG = SIMPLE size = parent_size
                                                      // otherwise size of "com" array 
} meta_info_t;

/*
for STACK: index is the index to the array of locals
for HEAP: index is the key to the hashtable
for both: offset is the offset in bits form where the previous point
*/
typedef struct ind_off {
	char  type;
	int   index;
	int   offset;
} index_t;

typedef struct global_struct {
	int     offset1;
	int     offset2;
	char *  handle; 					//for global struct/lock 
	char ** handle_ptr;   		//for global struct/lock pointer
} global_t;

typedef union kind {
	int                   offset;              //KIND = STACK
	index_t               io_elt;              //KIND = HEAP
	global_t              gs_elt; 		         //KIND = GLOBAL_I_*
	struct node *         com;                  //TAG is PATH or SEQ -- sequence of paths
									                            //and simple elements or a path
									                            //element with multiple paths
} kind_t;

typedef  struct node {
  meta_info_t     meta_info;            // 4 bytes
  kind_t          kind;                 // sizeof(void *)
  const char *    node_name;
} node_t;

typedef struct mypthread_mutex {
  pthread_mutex_t mutex;
  char * name;
} mypthread_mutex_t;



typedef struct stack_node {
  struct stack_node * next;
  node_t *current; /*DO NOT CHANGE node_t here*/
	mypthread_mutex_t ** locals;

  int fun_malloc_array_start;
} stack_node_t;


#define EXTERN
extern __thread int * global_malloc_array;
extern __thread int global_malloc_array_ind;

extern __thread stack_node_t *stack;
extern int mypthread_mutex_lock (mypthread_mutex_t *lock);

extern int mypthread_cond_wait (pthread_cond_t *cond,
                                mypthread_mutex_t *mutex);

extern int main (int argc, char * argv[]);


extern /*static*/ unsigned int  hashfromkey(void *ky);
extern /*static*/ int           equalkeys(void *k1, void *k2);
extern struct key *       create_key (int num);
extern struct value *     create_value (void * p);
extern struct key_inv *   create_key_inv (void * p);
extern struct value_inv * create_value_inv (int p);


extern void           print_hash(struct hashtable * h);
extern struct         hashtable_itr * hashtable_iterator(struct hashtable *h);
extern inline void *  hashtable_iterator_key(struct hashtable_itr *i);
extern inline void *  hashtable_iterator_value(struct hashtable_itr *i);
extern int            hashtable_iterator_advance(struct hashtable_itr *itr); 
extern void           ins_lock(int num, mypthread_mutex_t * p);
extern void           rem_lock(int num);
extern void           rem_lock_inv(void * p);
extern void           init_hashtbl (char * name);
extern void           exit_fun();

/**
 * The following specify key - value pairs for the heap hashtable.
 * */
struct key {
	int num;
};

struct value {
	void * lock_addr;
};


struct key_inv {
	void * lock_addr;
};

struct value_inv {
	int num;
};

stack_node_t dummy___stack;     /// HACK: force CIL to include stack_node_t

//the following must be undefined in runtime.c
#ifndef ___RUNTIME__
#define pthread_mutex_t mypthread_mutex_t
#define pthread_mutex_lock mypthread_mutex_lock
#define pthread_mutex_unlock mypthread_mutex_unlock
#define pthread_cond_wait mypthread_cond_wait

//#ifndef __LOCKSET_COUNT_
//#define main project_main
//#endif

#endif

#endif
