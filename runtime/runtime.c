/* Authors: Prodromos Gerakios and Nikolaos Papaspyrou
 *
 * All rights reserved.
 */
//#define NDEBUG  //remove assert code
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <sys/types.h>
#include <unistd.h>
#include <errno.h>
#include <sched.h>
#include <sys/syscall.h>
#include <string.h>
#include <stdint.h>
// DO NOT REMOVE __RUNTIME__
// MUST BE DEFINED BEFORE runtime.h
#define  ___RUNTIME__
//#define  ___LOCKSET_COUNT__
#include "runtime.h"

//changes
#include "hashtable.h"
#include "hashtable_itr.h"

#ifdef USE_BOEHM
#include "libatomic_ops/src/atomic_ops.h"
#endif

#define MAX_FUTURE_LOCKSET 256
#define MAX_CACHE          4

void futex_wake (int *addr, int count);
void futex_wait (int *addr, int val);
void simple_futex_wait(int *addr, int val);

#define cpu_relax() __asm__ __volatile__ ("rep; nop" ::: "memory")

pid_t gettid ()
{
  return syscall(SYS_gettid);
}

#ifdef DEBUG
int detail_level = 2;
__thread char debug_buff[4096];
#define dprintf(detail, ...)                                            \
  do {                                                                  \
    if (detail <= detail_level) {                                       \
      char *dbg = debug_buff;                                           \
      dbg += sprintf(dbg, "[%s:%d] ", __FILE__, __LINE__);              \
      dbg += sprintf(dbg, "[pid=%u] ", (unsigned) gthread_pid);         \
      sprintf(dbg, __VA_ARGS__);                                        \
      puts(debug_buff);                                                 \
      fflush(stdout);                                                   \
    }                                                                   \
  } while(0)

#define ddprintf(detail, ...)                   \
  do {                                          \
    if (detail <= detail_level) {               \
      char *dbg = debug_buff;                   \
      sprintf(dbg, __VA_ARGS__);                \
      puts(debug_buff);                         \
      fflush(stdout);                           \
    }                                           \
  } while(0)
#else
#define dprintf(...)
#define ddprintf(...)
#endif

#define implies(a,b) (!(a) || (b))

__thread pid_t gthread_pid = -1;


/*****************************************************************************
 *
 * 							Lockset count functions
 *
 *****************************************************************************/

//#define COUNT_LOCKSET
#ifdef COUNT_LOCKSET
unsigned long int count_lockset = 0;
unsigned long int sum_lockset = 0;
int max_lockset = 0;
int min_lockset = 0;
pthread_spinlock_t spinlock;
unsigned long int ls_counts[10] = {0,0,0,0,0,0,0,0,0,0};

void run_at_exit () {
  FILE * fp;
  fp = fopen("mylog.txt","w");


  unsigned long int sum = 0 ;
  int i = 0;
  for (i = 0 ; i < 10 ; i++) {
    sum += i * ls_counts[i];
  }

  double avg = sum_lockset / (count_lockset * 1.0) ;
/*  fprintf(fp,"min\t%d\nmax\t%d\naverage\t%lf\nchecks\t%ld\n\
lockset 0: %ld\nlockset 1: %ld\nlockset 2: %ld\nlockset 3: %ld\n\
lockset 4: %ld\nlockset 5: %ld\nlockset 6: %ld\nlockset 7: %ld\n\
lockset 8: %ld\nlockset 9: %ld\nsanity_sum %ld = %ld\n",
      min_lockset, max_lockset, avg, count_lockset,
      ls_counts[0], ls_counts[1],
      ls_counts[2], ls_counts[3],
      ls_counts[4], ls_counts[5],
      ls_counts[6], ls_counts[7],
      ls_counts[8], ls_counts[9],sum, sum_lockset );*/
   fprintf(fp,"%d\n%d\n%lf\n%ld\n%ld\n%ld\n%ld\n%ld\n%ld\n%ld\n%ld\n%ld\n%ld\n%ld\n",
      min_lockset, max_lockset, avg, count_lockset,
      ls_counts[0], ls_counts[1],
      ls_counts[2], ls_counts[3],
      ls_counts[4], ls_counts[5],
      ls_counts[6], ls_counts[7],
      ls_counts[8], ls_counts[9] );

}

int main (int argc, char * argv[]) {
  pthread_spin_init(&spinlock,PTHREAD_PROCESS_SHARED);
  atexit(& run_at_exit);
  int ret =  project_main(argc, argv);
  return ret ;
}


#endif

/*****************************************************************************
 *
 * 							Hashtable functions
 *
 *****************************************************************************/ 							

DEFINE_HASHTABLE_INSERT(insert_some, struct key, struct value);
DEFINE_HASHTABLE_SEARCH(search_some, struct key, struct value);
DEFINE_HASHTABLE_REMOVE(remove_some, struct key, struct value);
DEFINE_HASHTABLE_ITERATOR_SEARCH(search_itr_some, struct key);

DEFINE_HASHTABLE_INSERT(insert_some_inv, struct key_inv, struct value_inv);
DEFINE_HASHTABLE_SEARCH(search_some_inv, struct key_inv, struct value_inv);
DEFINE_HASHTABLE_REMOVE(remove_some_inv, struct key_inv, struct value_inv);


__thread struct hashtable *htbl;
__thread struct hashtable *htbl_inv;
__thread int count_calls = 0;

#undef get16bits
#if (defined(__GNUC__) && defined(__i386__)) || defined(__WATCOMC__) \
  || defined(_MSC_VER) || defined (__BORLANDC__) || defined (__TURBOC__)
#define get16bits(d) (*((const uint16_t *) (d)))
#endif

#if !defined (get16bits)
#define get16bits(d) ((((uint32_t)(((const uint8_t *)(d))[1])) << 8)\
                       +(uint32_t)(((const uint8_t *)(d))[0]) )
#endif

/*static*/ unsigned int
hashfromkey(void *ky) {
  struct key *k = (struct key *)ky;	
	return (unsigned int) k->num;

}

/* keys: integers */
/*static*/ int
equalkeys(void *k1, void *k2)
{
	return ((((struct key *)k1)->num == ((struct key *)k2)->num) ?  1 : 0);
}

/*static*/ unsigned int
hashfromkey_inv (void *ky) {
  struct key_inv *k = (struct key_inv *)ky;	
	return (unsigned int) k->lock_addr;

}

/*static*/ int
equalkeys_inv (void *k1, void *k2)
{
	return ((((struct key_inv *)k1)->lock_addr == ((struct key_inv *)k2)->lock_addr) ?  1 : 0);
}

struct key * create_key (int num) {
	struct key * k;
	k = (struct key *) malloc(sizeof(struct key));
	k->num = num;
	return k;
}

struct value * create_value (/*mypthread_mutex_t*/ void * p) {
	struct value * v;
	v = (struct value *) malloc(sizeof(struct value));
	v->lock_addr = p;
	return v;
}

struct key_inv * create_key_inv (/*mypthread_mutex_t*/ void * p) {
	struct key_inv * k;
	k = (struct key_inv *) malloc(sizeof(struct key_inv));
	k->lock_addr = p;
	return k;
}

struct value_inv * create_value_inv (int num) {
	struct value_inv * v;
	v = (struct value_inv *) malloc(sizeof(struct value_inv));
	v->num = num;
	return v;
}

int is_root_fun () {
  if (count_calls == 0) 
    return 1;
  else 
    return 0;
}

#ifdef DEBUG
void print_hash(struct hashtable * h) {
  struct hashtable_itr *itr;
  struct key *k;
	struct value * v;
	itr = hashtable_iterator(h);
	gthread_pid = gettid();

	if (count_calls == 0) {
		dprintf(2,"print malloc hashtable (this should be empty):\n");
		if (hashtable_count(h) > 0)
		{
			do {
				k = hashtable_iterator_key(itr);
				v = hashtable_iterator_value(itr);
				dprintf(2,"[%d]\t-->\t%p", k->num, v->lock_addr);   
			} while (hashtable_iterator_advance(itr));
			dprintf(2,"----------------------------");
		}
	}
}
#endif

void init_hashtbl (char * name) {
	if (count_calls++ == 0) {
		gthread_pid = gettid();
		dprintf(1,"In %s. Creates new hashes.\n", name);
		htbl = create_hashtable(16, hashfromkey, equalkeys);
		if (NULL == htbl) exit(-1);				
		htbl_inv = create_hashtable(16, hashfromkey_inv, equalkeys_inv);
		if (NULL == htbl_inv) exit(-1);		
	}
	return;
}

void exit_fun() {
	if	(count_calls-- == 1) {
		dprintf(2, "Exiting thread.");
#ifdef DEBUG		
		print_hash(htbl);
#endif
	}
	return;
}

void ins_lock(int num, mypthread_mutex_t * p)  {
	struct key * k = create_key(num);
  struct value * v;
  struct key_inv * k_inv;
  dprintf(1,"About to nsert heap lock.\n"); 
  v = hashtable_search(htbl, k);
  if (v != NULL) {    
    k_inv = create_key_inv(v->lock_addr);
    hashtable_remove(htbl, k);
    hashtable_remove(htbl_inv, k_inv);
  }
  dprintf(1,"inserting heap lock: %d -> %p\n", num,p); 
  if (!insert_some(htbl,k,create_value(p))) exit(-1);
  k_inv = create_key_inv(p);
	if (!insert_some_inv(htbl_inv,k_inv,create_value_inv(num))) exit(-1);	
#ifdef DEBUG
	print_hash(htbl);
#endif	
	return;
}

void rem_lock(int num) {
	struct key * k = create_key(num);
	struct value * val ;
	val =	hashtable_remove(htbl, k);
	if ( val == NULL) {
		dprintf(1,"Removed nothing!! Probably because it was already gone.\n");
	}
	else {
		dprintf(1,"(rem_lock) Removing (%d->%p) from hashtable.",num,val->lock_addr);	
		void * p = val->lock_addr;
		struct key_inv * k_inv = create_key_inv(p);
		struct val_inv * val_inv;
		val_inv = (struct val_inv *) hashtable_remove(htbl_inv,k_inv);
		if (val_inv == NULL) {
			dprintf(1,"Definitely error: while attempting to remove an element from inverse hashtable!!\n");
		}
	}
#ifdef DEBUG
	print_hash(htbl);
#endif
	return;
}

void rem_lock_inv( void * p ) {
	struct key_inv * k_inv = create_key_inv(p);
	struct value_inv * val_inv ;
	val_inv = (struct value_inv *) hashtable_remove(htbl_inv, k_inv);
	
	if (val_inv == NULL) {
		dprintf(1,"RUNTIME ERROR: Attempting to remove a lock (dir/ind) that does not exist in hashtable!!\n");
	}
	else {
		dprintf(1,"(rem_lock_inv) Removing (%p->%d) from inverse hashtable.", p, val_inv->num);
		int num = val_inv->num;
		struct key * k = create_key(num);
		struct value * val;
		val = (struct value *) hashtable_remove(htbl,k);
		if (val == NULL) {
				dprintf(1,"Definitely error: Attempting to remove an element from hashtable!!\n");
			}
		}
#ifdef DEBUG	
		print_hash(htbl);	
#endif
		return;
	}


/*****************************************************************************
 *
 * 												Effect operations
 *
 *****************************************************************************/ 	

//temp
char dummy[10] = "dummy";


typedef struct future_lockset {
  mypthread_mutex_t *mutex;
} future_lockset_t;

__thread int * global_malloc_array;
__thread int global_malloc_array_ind;

__thread stack_node_t *     stack = 0;

__thread future_lockset_t   future_lockset[MAX_FUTURE_LOCKSET];

__thread future_lockset_t *   gfl_iter      = 0;
__thread mypthread_mutex_t *  glock         = 0;
__thread int                  glocks_found  = 0;
__thread stack_node_t *       gstack_iter   = 0;
__thread int                  gignore_first = 0;

int compute_lockset_frame (node_t *iter_node,
                           ulong offset,
                           int locks_found,
                           node_t *pop_until){
  node_t *iter_node_tmp;
  node_t *iter_path,*iter_path_end;
  int path_locks,ret_locks,ind;
  node_t n;
  mypthread_mutex_t ** tmp;

  assert(locks_found);
  assert(iter_node);
  assert(glock);
  assert((void *) gstack_iter > (void *) 100);

  while( iter_node && (locks_found)) {
    n = *iter_node;
    dprintf(2,"VISITING %s (%p) ",iter_node->node_name,iter_node);
		assert(iter_node->node_name);
		switch(n.meta_info.tag){
    //simple lock operation
      case SIMPLE:
        assert(offset == 0);
        mypthread_mutex_t *h;
        struct value * v;

        switch(n.meta_info.mem){
          //the lock pointer is passed as an argument
          case STACK:
            dprintf(2,"STACK ");
            h = (mypthread_mutex_t *) (gstack_iter->locals)[n.kind.offset];
            break;
          /* ( & (* base).offset )
           * handle_ptr = (char **) (& base) */
          case GLOBAL_DRF_HDL:
            dprintf(2,"GLOBAL_DEREFERENCED_HANDLE");
            h = (mypthread_mutex_t *) (((char *) *(n.kind.gs_elt.handle_ptr + n.kind.gs_elt.offset1)) +
                n.kind.gs_elt.offset2);
            break;
          /* ( & base.offset ) 
           * handle = (char *) base */
          case GLOBAL_NODRF_HDL:
            dprintf(2,"GLOBAL_NON-DEREFERENCED_HANDLE");
            h = (mypthread_mutex_t *) (((char *) n.kind.gs_elt.handle) + 
                n.kind.gs_elt.offset1 + n.kind.gs_elt.offset2);
            break;
          /* ( *(base).offset )
           * handle_ptr = (char **) (& base) */
          case GLOBAL_DRF_PTR:
            dprintf(2,"GLOBAL_DEREFERENCED_POINTER");
            tmp = (mypthread_mutex_t **) (((char *) *(n.kind.gs_elt.handle_ptr + n.kind.gs_elt.offset1)) +
                n.kind.gs_elt.offset2);
            if (tmp == NULL) assert(0);
            h = *tmp;

            break;
          /* ( base.offset ) probably offset = 0 */
          case GLOBAL_NODRF_PTR:
            dprintf(2,"GLOBAL_NON-DEREFERENCED_POINTER");
            tmp = (mypthread_mutex_t **) ((char **) n.kind.gs_elt.handle_ptr + 
                n.kind.gs_elt.offset1 + n.kind.gs_elt.offset2);
            if (tmp == NULL) assert(0);
            h = *tmp;
            break;


          case HEAP:
            /* if type == 0 then the malloced location escaped the function
             * so it's found with its offset in the malloc array */
            if (n.kind.io_elt.type) {
              ind = global_malloc_array[(gstack_iter->fun_malloc_array_start)
                + n.kind.io_elt.index];
              ddprintf(1,"\tWill look for: H[_a[%d] = %d] + %d",n.kind.io_elt.index,ind,
                n.kind.io_elt.offset);
              v = hashtable_search(htbl, create_key(ind));
              if (v != NULL) {
                h = (mypthread_mutex_t *) (((char *) v->lock_addr) + n.kind.io_elt.offset) ;
                ddprintf(1,"\tFound hash element: H[_a[%d] = %d] + %d -> %p",n.kind.io_elt.index,ind,
                  n.kind.io_elt.offset,h);
              }
              else {
                h = NULL;
              }
            }
            else {
            /* the malloced location's scope does not escape the function, so it
             * we search for it in the directly in the hashtable */
              ddprintf(1,"\tWill look for: H[%d] + %d",n.kind.io_elt.index,
                n.kind.io_elt.offset);
              v = hashtable_search(htbl,create_key(n.kind.io_elt.index));
              if (v != NULL) {
                h = (mypthread_mutex_t *) (((char *) v->lock_addr) + n.kind.io_elt.offset) ;
                ddprintf(1,"\tFound hash element: H[%d] + %d -> %p",n.kind.io_elt.index,
                    n.kind.io_elt.offset,h);
              }
              else {
                h = NULL;
              }
            }
            
            if (h == NULL) {
            //the lock doesn't exist yet - this is just ignored
#ifdef DEBUG
              print_hash(htbl);
#endif						
              ddprintf(1,"\tLock (H[(a)%d]) doesn't exist yet/anymore. This is ignored." , n.kind.io_elt.index);
            };
            break;
          default:
             assert(0); //impossible!
             break;
        }

        int type = (int) n.meta_info.type;
        if( h == glock ){
          if( gignore_first ) gignore_first = 0;
          else  locks_found += type;
        }
        // add to lockset
        else if ( type == LOCK && h ) {
          if( gfl_iter >= future_lockset + MAX_FUTURE_LOCKSET)
            exit(-1);
          (gfl_iter++)->mutex = h;

          ddprintf(2," LOCKSET ");
          h->name = (char *) iter_node->node_name;

        }
        ddprintf(2,"\n");
        if( n.meta_info.parent_offset+1 < n.meta_info.size){
          iter_node++; //next elt in sequence
          //dprintf("INCREMENTED iter_node = %p\n",iter_node);
          continue;
        }
        break;
        ///  ///    //       ///     ///       ///    //
			case PATH:
        for
        (//init
          ret_locks=-1,
          path_locks = locks_found,
          iter_path = n.kind.com + offset,
          iter_path_end = iter_path + n.meta_info.size;
          // condition
          locks_found &&
          iter_path < iter_path_end ;
          // repeat instr
          path_locks = locks_found,//reset path_locks
          iter_path++ )
        {
          dprintf(3,"ENTERING PATH: %s\n\n", iter_path->node_name);
          path_locks = compute_lockset_frame
                     (iter_path,0,
                      path_locks,
                      iter_node // pop until this node
                     );
          dprintf(3,"EXITING PATH\n\n");

          //If we don't find the corresponding unlock operation even 
          //in one of the paths, then we continue searching the rest of the
          //effect. We keep the biggest of all the path_lock counts for this.
          if( ret_locks == -1 ) {
            dprintf(4,"#######ret_locks = -1 while looking for%s, "
                  "pl=%d, rl=%d, glock=%s\n", iter_node->node_name, 
                  path_locks, ret_locks, glock->name);
            ret_locks = path_locks;
          }
          else {
            if (path_locks > ret_locks) {
              dprintf(4,"#######path_locks > ret_locks while looking for%s, "
                  "pl=%d, rl=%d, glock=%s\n", iter_node->node_name, 
                  path_locks, ret_locks, glock->name);
              ret_locks = path_locks;
            }
            else {
              dprintf(4,"#######path_locks = %d, ret_locks = %d while looking"
                  " for%s, glock=%s\n",  
                  path_locks, ret_locks, iter_node->node_name,glock->name);            
            }
          }
         }
        //running PATH will iterate over all possible paths
        //and will gather a set of locks belonging to any path
        locks_found = ret_locks;
        break;
        ///  ///    //       ///     ///       ///    //
			case SEQ:
        if( offset < n.meta_info.size ){
          dprintf(3,"LOOPING SEQ: offset=%ld size=%ld this-child=%ld\n\n",
                 (long)offset,
                 (long)n.meta_info.size,
                 (long) (n.kind.com - iter_node));
          iter_node = n.kind.com + offset;
          offset = 0;
          continue;
        }
        break;
			// /// //
			case CALL:
				if( n.kind.com ){
				// optimization: a null pointer is passed 
				// for functions with empty effects
					dprintf(3,"ENTERING CALL:\n\n");
					locks_found = compute_lockset_frame
										 (n.kind.com,0,locks_found,0);
					dprintf(3,"EXITING CALL\n\n");
				}
			break;
			default:
				assert(0); //impossible!
			break;
		}

		dprintf(4,"starting with OLD node %s | POP UNTIL = %s\n",
			iter_node->node_name,
			pop_until?pop_until->node_name:"next path");

    // go some levels up if necessary
		int cond[3] = {0,0,0};
		do {
			if(!n.meta_info.has_parent) {
				dprintf(4,"returning to parent\n");
				return locks_found;
			}
			// parent node is n places back
			iter_node_tmp = iter_node - n.meta_info.parent;
			dprintf(4,"C1=%d C2=%d C3=%d\nThis->node = %s parent_offset=%d\n",
  			cond[0],cond[1],cond[2],
	  		iter_node->node_name,(int)  n.meta_info.parent_offset);
			offset = n.meta_info.parent_offset; //this elt
			assert(offset <  iter_node_tmp->meta_info.size);
			offset++; // next elt
			dprintf(4,"next = %s, next->size=%ld, this->offset+1=%ld\t"
				"Skipping this->node : %s\n",
				iter_node_tmp->node_name ,
				(long) iter_node_tmp->meta_info.size,
				(long) offset,
				iter_node->node_name);

			iter_node = iter_node_tmp;
			n = *iter_node;

		} while( (
        (cond[0]=(offset >= n.meta_info.size))
        ||
        (cond[1]=(n.meta_info.tag == PATH))
        )
        &&
        (cond[2]=implies(pop_until,iter_node != pop_until))
			//||
			//(cond[1]=(!pop_until &&
			// n.meta_info.tag == PATH)))
			//||
			//(cond[2]=(pop_until &&
			// iter_node != pop_until)
			//)
		);
		dprintf(4,"C1=%d C2=%d C3=%d\nNEW iter_node = %s offset=%ld, locks_found=%d\n",
			cond[0],cond[1],cond[2],
			iter_node->node_name,(long) offset,
      locks_found);
		if( iter_node == pop_until) break;
	}
	return locks_found;
}

#ifdef USE_BOEHM
#define __sync_fetch_and_add(a,b) AO_fetch_and_add_full(a,b)
#define __sync_fetch_and_sub(a,b) AO_fetch_and_add_full(a,-b)
#endif

void compute_lockset ()
{

  assert(glock);
  assert(glocks_found);
  assert((void *)stack > (void *)100);
  assert(stack->current);
  assert(stack->current->meta_info.type == LOCK);

  if(!glock->name){
    glock->name = (char *) stack->current->node_name;
  }

  dprintf(1,"lockset computation for: %s (%p)\n",glock->name,glock);
	int i =0 ;
  // Iterate over the stack frames
  for(gstack_iter = stack;
      glocks_found && gstack_iter ;
      gstack_iter = gstack_iter->next){

    glocks_found = compute_lockset_frame(gstack_iter->current,
                              0,/*gstack_iter->offset,*/glocks_found,0);
  }
  dprintf(1,"lockset computation for %s (%p) done.\n", glock->name, glock);
#ifdef DEBUG
  future_lockset_t * cu;
  dprintf(1,"LOCKSET: ");
  for( cu = future_lockset; cu < gfl_iter  ; cu++){
    dprintf(1,"%s || addr: %p", cu->mutex?cu->mutex->name:"(null)", cu->mutex);
  }
 	dprintf(1,"END OF LOCKSET\n");
#endif

#ifdef COUNT_LOCKSET

  pthread_spin_lock(&spinlock);
  future_lockset_t * cu1;
  int cnt = 0;
  for( cu1 = future_lockset; cu1 < gfl_iter  ; cu1++) cnt++ ;
//  __sync_fetch_and_add(&count_lockset, 1);
//  __sync_fetch_and_add(&sum_lockset, cnt);
  sum_lockset += cnt;
  count_lockset ++;
  ls_counts[cnt]++;
  if (max_lockset < cnt) max_lockset = cnt;
  if (min_lockset > cnt) min_lockset = cnt;
  pthread_spin_unlock(&spinlock);

#endif

}

int mypthread_mutex_lock (mypthread_mutex_t *lock)
{

#ifdef DEBUG
  if (detail_level == -1) {
    char *env = getenv("DETAIL_LEVEL"), c;
		printf("detail level: %s\n\n", env);
    if (!env)
      detail_level = 0;
    else {
      c = *env;
      detail_level = (c < '1' || c > '9') ? 0 : c - '0';
    }
  }
#endif

  if (!lock) return 0;

  // store my own thread id for future use
  if (gthread_pid == -1) gthread_pid = gettid();

  // already locked by me: no need to check future lockset
  if (((pthread_mutex_t *)lock)->__data.__owner == gthread_pid) {
    dprintf(0, "LOCK ALREADY HELD for %u on %s\n",
            (unsigned) gthread_pid, lock ? lock->name : "(null)");
    return pthread_mutex_lock((pthread_mutex_t *) lock);
  }

  // compute future lockset
  glock = lock;               // DO NOT MOVE req by compute_lockset
  glocks_found = 1;           // DO NOT MOVE req by compute_lockset
  gfl_iter = future_lockset;  // end of future lockset
  gignore_first = 1;
  compute_lockset();

  future_lockset_t *cu;
  int lock_val, ret;
#ifdef __FUTEX__
  pthread_mutex_t *wt = NULL;
#endif

  // loop until successful
RETRY:
  // check that all locks in future lockset are now available
  for (cu = future_lockset; cu < gfl_iter; cu++) {
    if (cu->mutex == NULL) continue;
    if (cu->mutex->mutex.__data.__owner == gthread_pid) {
      cu->mutex = NULL; // already owned by me, ignore from now on
      continue;
    }
    lock_val = __sync_fetch_and_add(&cu->mutex->mutex.__data.__lock, 0);
    if (lock_val != 0) {
    //if the lock is held by another thread, initialize the futex on the lock 
    //we are trying to acquire
#ifdef __FUTEX__
      if (wt != NULL) futex_wake(&wt->__data.__lock, 1);
      wt = (pthread_mutex_t *) cu->mutex;
#endif
      dprintf(0, "future lock %s not available (first check) (value %d) (addr: %p)\n",
              cu->mutex ? ((mypthread_mutex_t *) cu->mutex)->name : "(null)",
              lock_val, cu->mutex);
      goto YIELD;
    }
  }
  // lock tentatively (possibly suspending)
#ifdef __FUTEX__
  if (wt != NULL) { futex_wake(&wt->__data.__lock, 1); wt = NULL; }
#endif
  ret = pthread_mutex_lock((pthread_mutex_t *) lock);
  if (ret != 0) return ret;
  dprintf(0, "wanted lock %s acquired tentatively\n",
          lock ? ((mypthread_mutex_t *) lock)->name : "(null)");
  // check that versions did not change
  for (cu = future_lockset; cu < gfl_iter; cu++) {
    if (cu->mutex == NULL) continue;
    if (cu->mutex->mutex.__data.__owner == gthread_pid) continue;
    lock_val = __sync_fetch_and_add(&cu->mutex->mutex.__data.__lock, 0);
    if (lock_val != 0) {
      dprintf(0, "future lock %s not available (value %d)\n",
              cu->mutex ? ((mypthread_mutex_t *) cu->mutex)->name : "(null)",
              lock_val);
      pthread_mutex_unlock((pthread_mutex_t *) lock);
      dprintf(0, "wanted lock %s released\n",
              lock ? ((mypthread_mutex_t *) lock)->name : "(null)");
#ifdef __FUTEX__
      if (wt != NULL) futex_wake(&wt->__data.__lock, 1);
      wt = (pthread_mutex_t *) cu->mutex;
#endif
      goto YIELD;
    }
  }
  // successful
#ifdef __FUTEX__
  if (wt != NULL) { futex_wake(&wt->__data.__lock, 1); wt = NULL; }
#endif
  dprintf(0, "LOCK SUCCESSFUL on %s\n", lock ? lock->name : "(null)");
  return 0;

YIELD:
#ifdef __FUTEX__
  if (lock_val != 2) {
    __sync_bool_compare_and_swap(&wt->__data.__lock, 1, 2);
    lock_val = 2;
  }
  dprintf(0, "FUTEX on %s value %d\n",
          wt ? ((mypthread_mutex_t *) wt)->name : "(null)", lock_val);
  futex_wait(&wt->__data.__lock, lock_val);
  dprintf(0, "FUTEX woken\n");
#else
#ifdef __YIELD__
  dprintf(0, "YIELDING\n");
  sched_yield();
#else
#ifdef __BUSY__
  cpu_relax();
#else
#error "Define exactly one of __FUTEX__, __YIELD__ or __BUSY__"
#endif
#endif
#endif
  goto RETRY;
}

int mypthread_mutex_unlock (mypthread_mutex_t *lock)
{
  int ret = pthread_mutex_unlock((pthread_mutex_t *) lock);
  dprintf(0, "UNLOCK SUCCESSFUL on %s\n", lock ? lock->name : "(null)");
  return ret;
}

int mypthread_cond_wait(pthread_cond_t *cond, mypthread_mutex_t *mutex)
{
  int ret = pthread_cond_wait(cond, (pthread_mutex_t *) mutex);
  mypthread_mutex_unlock(mutex);
  mypthread_mutex_lock(mutex);
  return ret;
}

