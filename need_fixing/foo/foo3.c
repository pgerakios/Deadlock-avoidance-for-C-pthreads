#include <stdlib.h>
#include <pthread.h>

pthread_mutex_t * l1;
pthread_mutex_t * l2;

struct relevant {
  int a;
  int b; 
  pthread_mutex_t * lock;
  struct relevant * ab;
};

struct relevant * irr;
pthread_mutex_t gl1;
pthread_mutex_t gl2;
pthread_mutex_t gl3;

void * f ()
{

  irr = (struct relevant *) malloc(sizeof(struct relevant));
  irr->a = 5;
  irr->b = 42;  
  irr->ab = irr;
  l2 = &gl1;
  pthread_mutex_t * tmp;
  tmp = &gl3;

  if (irr->a ) { l1 = tmp; l1 = &gl3; l1 = &gl2; } 
  else { l1 = &gl1; l1 = &gl2; 
    if (irr->b) { tmp = &gl2; l1 = tmp; }
    else { l1 = &gl3; l1 = &gl1; l1 = &gl2; }  
  }
  
// Do we support this?
//  pthread_mutex_t ** r;
//  r = &irr->lock;
//  *r = &l1;
}

void * f1 (pthread_mutex_t * arg1) 
{
  l1 = arg1;
  arg1 = &gl2; //should not make any change
}

void * f2 (struct relevant * arg2) 
{
  struct relevant * tmp = arg2;
  l1 = arg2->lock;
  tmp->lock = &gl1;
//uncommenting this changes main's effect  
//  arg2 = malloc(sizeof(struct relevant)); 
  arg2->lock = malloc(sizeof(pthread_mutex_t));
}


int main ()
{
  f();
  pthread_mutex_lock(l1);
  pthread_mutex_lock(l2);
  pthread_mutex_unlock(l2);
  pthread_mutex_unlock(l1);

  struct relevant * r ;
 r = malloc(sizeof(struct relevant));
  r->lock = malloc(sizeof(pthread_mutex_t));

  f1(&gl3);
  pthread_mutex_lock(l1);
  pthread_mutex_unlock(l1);  
  f2(r);
  pthread_mutex_lock(r->lock);
  pthread_mutex_unlock(r->lock);
  return 0;
}
