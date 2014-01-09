/* Authors: Prodromos Gerakios 
 *
 * All rights reserved.
 */
#include "runtime.h"
/////////////////////////////////////////////////////
#include <stdio.h> 

void *thread(void *arg){
 return 0;
}

int main(int argc, char *argv[] ){
 mypthread_mutex_t p0,p1,p2,p3;
 pthread_t t0; 

 thread(&t0);// useless but we don't want the compiler to
             // remove this variable
  //pthread_create(&t0,0,thread,0);
  stack_node_t s; 
  node_t n0[11];


// printf("\n &s = %p\nt0= %p\np3=%p\n",
  //      &s,&t0,&p3);  
#define SZ(A)    printf("sizeof(%s)=%ld\n",#A,(long)sizeof(A))
#define D(A,B) \
  printf("&%s - &%s = %ld\n",#A,#B,(long) ((long)&A - (long) &B))
#define NL printf("\n")
#define S(a) sizeof(a)
#define P(a,b,c,d) printf("%s+%s+%s*%s= %ld\n",\
                  #a,#b,#c,#d,(long) (S(a)+S(b)+c*S(d)));      

 SZ(stack_node_t);
 SZ(pthread_t);
 SZ(mypthread_mutex_t);
 D(p0,p1);
 D(p1,p2);
 D(p2,p3);
 D(p3,t0);
 D(t0,s);

 NL;
 D(p0,s);
 P(stack_node_t,pthread_t,3,mypthread_mutex_t);

 NL;
 D(p1,s);
 P(stack_node_t,pthread_t,2,mypthread_mutex_t);

 NL;
 D(p2,s);
 P(stack_node_t,pthread_t,1,mypthread_mutex_t);

 NL;
 D(p3,s);
 P(stack_node_t,pthread_t,0,mypthread_mutex_t);

// exit(0);
//
  p0.name = "p0";
  p1.name = "p1";
  p2.name = "p2";
  p3.name = "p3";

#define OFF(x)  sizeof(stack_node_t)+\
                sizeof(pthread_t)+\
                 (x) * sizeof(mypthread_mutex_t)

  n0[0].meta_info.tag = SEQ;
  n0[0].meta_info.has_parent = 0;
  n0[0].meta_info.size = 4;
  n0[0].kind.com = n0+0+1;
  n0[0].node_name = "SEQ @0";

  n0[1].meta_info.tag = SIMPLE;
  n0[1].meta_info.type = LOCK; 
  n0[1].meta_info.mem = STACK; 
  n0[1].meta_info.has_parent = 1;
  n0[1].meta_info.parent = 1; //offset from parent
  n0[1].meta_info.parent_offset = 0;
  n0[1].meta_info.size = 3; //parent size
  n0[1].kind.stack_offset = OFF(3);
  n0[1].node_name = "SIMPLE @1: &p0";

  n0[2].meta_info.tag = SIMPLE;
  n0[2].meta_info.type = LOCK; 
  n0[2].meta_info.mem= STACK; 
  n0[2].meta_info.has_parent = 1;
  n0[2].meta_info.parent = 2; //offset from parent
  n0[2].meta_info.parent_offset = 1;
  n0[2].meta_info.size = 3; //parent size
  n0[2].kind.stack_offset = OFF(2);
  n0[2].node_name = "SIMPLE @2: &p1";

  n0[3].meta_info.tag = PATH;
  n0[3].meta_info.has_parent = 1;
  n0[3].meta_info.parent = 3; //offset from parent
  n0[3].meta_info.parent_offset = 2;
  n0[3].meta_info.size = 2; // paths
  n0[3].kind.com = n0+3+2;
  n0[3].node_name = "PATH @ 3";
 
  n0[4].meta_info.tag = SIMPLE;
  n0[4].meta_info.type = LOCK; 
  n0[4].meta_info.mem = STACK; 
  n0[4].meta_info.has_parent = 1;
  n0[4].meta_info.parent = 4; //offset from parent
  n0[4].meta_info.parent_offset = 3;
  n0[4].meta_info.size = 4; //parent size
  n0[4].kind.stack_offset = OFF(3);
  n0[4].node_name = "SIMPLE @ 4: &p0";

  n0[5].meta_info.tag = SEQ;
  n0[5].meta_info.has_parent = 1;
  n0[5].meta_info.parent = 2; //offset from parent
  n0[5].meta_info.parent_offset = 0;
  n0[5].meta_info.size = 2; 
  n0[5].kind.com = n0+5+2; // ?
  n0[5].node_name = "SEQ @ 5";

  n0[6].meta_info.tag = SEQ;
  n0[6].meta_info.has_parent = 1;
  n0[6].meta_info.parent = 3; //offset from parent
  n0[6].meta_info.parent_offset = 1;
  n0[6].meta_info.size = 2; 
  n0[6].kind.com = n0+6+3; // ?
  n0[6].node_name = "SEQ @ 6";


  n0[7].meta_info.tag = SIMPLE;
  n0[7].meta_info.type = LOCK; 
  n0[7].meta_info.mem = STACK; 
  n0[7].meta_info.has_parent = 1;
  n0[7].meta_info.parent = 2; //offset from parent
  n0[7].meta_info.parent_offset = 0;
  n0[7].meta_info.size = 2; //parent size
  n0[7].kind.stack_offset = OFF(1);//p2
  n0[7].node_name = "SIMPLE @ 7: &p2";

  n0[8].meta_info.tag = SIMPLE;
  n0[8].meta_info.type = LOCK; 
  n0[8].meta_info.mem = STACK; 
  n0[8].meta_info.has_parent = 1;
  n0[8].meta_info.parent = 3; //offset from parent
  n0[8].meta_info.parent_offset = 1;
  n0[8].meta_info.size = 2; //parent size
  n0[8].kind.stack_offset = OFF(0);//p3
  n0[8].node_name = "SIMPLE @ 8: &p3";


  n0[9].meta_info.tag = SIMPLE;
  n0[9].meta_info.type = LOCK; 
  n0[9].meta_info.mem = STACK; 
  n0[9].meta_info.has_parent = 1;
  n0[9].meta_info.parent = 3; //offset from parent
  n0[9].meta_info.parent_offset = 0;
  n0[9].meta_info.size = 2; //parent size
  n0[9].kind.stack_offset = OFF(0);//p3
  n0[9].node_name = "SIMPLE @ 9: &p3";

  n0[10].meta_info.tag = SIMPLE;
  n0[10].meta_info.type = LOCK; 
  n0[10].meta_info.mem = STACK; 
  n0[10].meta_info.has_parent = 1;
  n0[10].meta_info.parent = 4; //offset from parent
  n0[10].meta_info.parent_offset = 1;
  n0[10].meta_info.size = 2; //parent size
  n0[10].kind.stack_offset = OFF(1); //p2
  n0[10].node_name = "SIMPLE @ 10: &p2";

  // body of function main
  
  pthread_mutex_init(&p0,0);
  pthread_mutex_init(&p1,0);
  pthread_mutex_init(&p2,0);
  pthread_mutex_init(&p3,0);

  printf("\np0=%p\np1=%p\np2=%p\np3=%p\n",
         &p0,&p1,&p2,&p3);
  int i = 0;
  for(i =0 ; i  < 11 ; i++ )
     printf("n0+%d  = %p\n",i,n0+i);

  s.next = stack;
  stack = &s;

  s.current = n0+1;
  mypthread_mutex_lock(&p0);

  s.current = n0+2;
  mypthread_mutex_lock(&p1);

  if(argc){
    s.current = n0+7;
    mypthread_mutex_lock(&p2);
    s.current = n0+8;
    mypthread_mutex_lock(&p3);
  } else {
    s.current = n0+9;
    mypthread_mutex_lock(&p3);
    s.current = n0+10;
    mypthread_mutex_lock(&p2);
  }
  
 // s.current = n0+4;
 // mypthread_mutex_lock(&p1);

 return 0; 
}
