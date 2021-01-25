//--------------------------------------------------------------------
//
//  4190.307: Operating Systems (Spring 2020)
//
//  PA#6: Kernel Threads
//
//  June 2, 2020
//
//  Jin-Soo Kim
//  Systems Software and Architecture Laboratory
//  Department of Computer Science and Engineering
//  Seoul National University
//
//
//  June 21, 2020
//  ChanHee Cho 
//  Department of Mathematical Sciences 
//  Department of Computer Science and Engineering
//  Seoul National University
//  
//--------------------------------------------------------------------

#include "types.h"
#include "param.h"
#include "memlayout.h"
#include "riscv.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "proc.h"
#include "defs.h"

#ifdef SNU

extern pagetable_t kernel_pagetable;
extern struct proc proc[];


// A kthread's very first scheduling by scheduler()
// will swtch to kth_cret_ret
void
kth_cret_ret(void)
{
  // Still holding p->lock from scheduler.
  struct proc *p = myproc();
  void (*fn)(void *) = p->fn;
  void *arg          = p->arg;

  release(&p->lock);

  // Jump into the fn, never to return.
  fn(arg);
  panic("kthread_create_return() exit. aka kth_cret_ret()");

}


// Look in the process table for an UNUSED proc.
// If found, initialize state required to run in the kernel,
// In case of no free procs or invalid prio,  return -1.
int 
kthread_create(const char *name, int prio, void (*fn)(void *), void *arg)
{
  struct proc *p;
  int tid;
  uint64 sp;
  
 // printf("arg(pointer value): %p\n", arg);

  // prio should be in range of [0,99].
  if( (prio < 0) || (prio > 99) )
      return -1;

  // traverse proc array to find UNUSED 'struct proc'.
  for(p = proc; p < &proc[NPROC]; p++) {
    acquire(&p->lock);
    if(p->state == UNUSED) {
      goto found;
    } else {
      release(&p->lock);
    }
  }
  return -1;


// note that we are holding p->lock
found:
  p->pid = allocpid();
  tid = p->pid;

  // No need to allocate a trapframe page / user page table
  // No need to set   p->sz / p->ofile
  // p->parent?   p->cwd? 
  p->pagetable = kernel_pagetable;

  // Set up new context to start executing at kth_cret_ret
  memset(&p->context, 0, sizeof p->context);
  p->context.ra = (uint64)kth_cret_ret;
  sp = p->kstack + PGSIZE;   
  p->context.sp = sp;

  // see proc.h and kth_cret_ret() for details.
  p->arg = arg; 
  p->fn = fn;


  safestrcpy(p->name, name, sizeof(p->name));

  p->cwd = namei("/");

  p->bprio = prio;
  p->eprio = prio;
  p->waiting_for = 0;
  p->dona_next = 0;
  p->dona_list = 0;

  p->state = RUNNABLE;
  release(&p->lock);

  // yield if new_thread has higher priority
  if(prio < kthread_get_prio())
      kthread_yield();

  return tid;
}



// free a proc structure and the data hanging from it.
// how to make sure this thread does not hold any sleeplock 
// before exit? 
// not holding any spinlock except for p->lock is guaranteed 
// by checking n->off in sched().
void 
kthread_exit(void)
{
//  printf("kthread_exit():hi\n");
  struct proc *p = myproc();


  acquire(&p->lock);
  p->tf = 0;
  p->pagetable = 0;
  p->sz = 0;
  p->pid = 0;
  p->parent = 0;
  p->name[0] = 0;
  p->chan = 0;
  p->killed = 0;
  p->bprio = -1;
  p->eprio = -1;
  p->xstate = 0;
  p->state = UNUSED;
  p->waiting_for = 0;
  p->dona_next = 0;
  p->dona_list = 0;


  // Jump into the scheduler, never to return.
  sched();
  panic("dead kthread exit");
}


void
kthread_yield(void)
{
  yield();
}


void
kthread_set_prio(int newprio)
{
  struct proc *p = myproc();
  int original_eprio;
  int new_eprio;
  
  acquire(&p->lock);
  original_eprio = p->eprio;
  p->bprio = newprio;
  release(&p->lock);

  new_eprio = refresh_eprio();
  
  // note that lower 'prio'value indicates higher priority.
  // if this thread became less important, yield.
  if(new_eprio > original_eprio)
      kthread_yield();
}

int
kthread_get_prio(void)
{
  struct proc *p = myproc();
  int eprio;
  acquire(&p->lock);
  eprio = p->eprio;
  release(&p->lock);
  return eprio;
}
#endif

