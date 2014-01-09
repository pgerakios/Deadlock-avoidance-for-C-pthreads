#include <stdlib.h>
#include <pthread.h>

struct inner {
  pthread_mutex_t * ip;
};

struct str {
  pthread_mutex_t * p;
  struct inner * in;
};
pthread_mutex_t gl;
pthread_mutex_t lr;

void f (pthread_mutex_t *q)
{
  // this should NOT be added to summary
  //  pthread_mutex_t a;
  pthread_mutex_t *r;
  r = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));;
  q = r;
  //  pthread_mutex_lock(&a);
}

void f2 (struct str *p2, struct str *q2,struct str *s2)
{
  pthread_mutex_t * r1;
  pthread_mutex_t * r2;
  // this should be added to summary  
  r1 = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));
  r2 = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));

  p2->in->ip = r2;
  q2->in->ip = r2;
  s2->in->ip = r1;
//  pthread_mutex_lock(r1);
}

void f1 (struct str *p, struct str *q,struct str *r,struct str *s)
{
  pthread_mutex_t * r1;
  pthread_mutex_t * r2;
  // this should be added to summary  
  r1 = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));
  r2 = (pthread_mutex_t * ) malloc(sizeof(pthread_mutex_t));

/*
  if (r1) { q->p = r2; s->in->ip = r2; r->in->ip = r1; }
  else { q->p = r2; s->in->ip = r2; r->in->ip = r1; }    
*/
  p->p = r1;
  f2(p,q,s);
/*
  p->p = r;
  p->in->ip = r;
  p = malloc(sizeof(struct str));
  q = p;
*/
}

int main ()
{
  struct str a;
  a.p = &gl;
  pthread_mutex_t * l1 = a.p;
//  f(r.p);

  pthread_mutex_t * l2 = a.p;
  f1(&a,&a,&a,&a);
  pthread_mutex_lock(a.p);
  pthread_mutex_lock(a.in->ip);
  pthread_mutex_unlock(a.in->ip);
  pthread_mutex_unlock(a.p);

  return 0;
}
