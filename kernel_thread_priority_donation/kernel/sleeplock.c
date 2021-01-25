// Sleeping locks

#include "types.h"
#include "riscv.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "spinlock.h"
#include "proc.h"
#include "sleeplock.h"

extern struct proc proc[];
struct spinlock tree_lock;

// refresh eprio and return refreshed eprio.
// refresh by finding  minimum priority 
// between p->bprio, and eprio of childs.
int
refresh_eprio(void)
{
  struct proc *p = myproc();  
  int min_eprio;
  struct proc *next, *tmp;


//  acquire(&p->lock);
  min_eprio = p->bprio;   
  next = p->dona_list;
//  release(&p->lock);

  while(next != 0) {
//      acquire(&next->lock);
      if(min_eprio > next->eprio)
          min_eprio = next->eprio;
      tmp = next->dona_next;
//      release(&next->lock);
      next = tmp;
  }

//  acquire(&p->lock);
  p->eprio = min_eprio;
//  release(&p->lock);

  return min_eprio;
}

// should be called without any p->lock held.
struct proc* 
find_proc_with_pid(int pid) {
   struct proc *p;
   for(p = proc; p < &proc[NPROC]; p++){
//     acquire(&p->lock);
     if(p->pid == pid)
         break;
//     release(&p->lock);
   }
//   release(&p->lock);
   return p;
}



// only used in acquiresleep() , collect_orphans().
// lock ordering?????   lk->ik then p->lock ?? 
void
insert_and_update(struct proc *node, struct proc *parent, struct sleeplock *lk) {
  //lk->lk is held - cannot release to catch all wakeups.
  struct sleeplock *parent_lk;
  int parent_pid;

  //insert node
  //@@@implement using locks@@@@TODO
  if(parent->dona_list == 0) {
      parent->dona_list = node;
      node->dona_next = 0;   // just to make sure.
  }
  else {
      node->dona_next = parent->dona_list;
      parent->dona_list = node;
  }


  // update eprio up to the root 
  // if node's eprio is low then current eprio, do not need to go more.
  while(parent != 0) {
      if(parent->eprio > node->eprio)
          parent->eprio = node->eprio;
      else
          return;

      parent_lk = parent->waiting_for;

      if(parent_lk == 0)
          return;

//      acquire(&parent_lk->lk);
      parent_pid = parent_lk->pid;
//      release(&parent_lk->lk);
      
      parent = find_proc_with_pid(parent_pid);
  }
}


//only used in releasesleep()
//traverse p->dona_list and remove nodes who are waiting for lk
//
//below comment is implemented in acquiresleep(). 
//if there were multiple nodes waiting for lk,
//the firstly scheduled one will acquire lk and make all orphans its child.
//see acquiresleep() for this.
void
remove_lk_children(struct sleeplock *lk) {
  struct proc *p = myproc();
  struct proc *curr, *next, *tmp;

  curr = p;
  next = p->dona_list;
  
  while(next != 0) {

      if(next->waiting_for == lk) {
          //remove
          tmp = next;

          if(curr == p) {
              p->dona_list = next->dona_next;
              next = p->dona_list;

              // tidy-up
              tmp->dona_next = 0;
              continue;
          }

          else {
              curr->dona_next = next->dona_next;
              next = next->dona_next;
            
              // tidy-up
              tmp->dona_next = 0;
              continue;
          }
      }
      curr = next;
      next = next->dona_next;
 }
}


// only used in acquiresleep()
// should be called without any p->lock held.
// after acquiring lk, make threads that are 
// waiting for lk my children.
void
collect_orphans(struct sleeplock *lk) {
   struct proc *p;
   //TODO use lock
   for(p = proc; p < &proc[NPROC]; p++){
     if(p->waiting_for == lk)
         insert_and_update(p, myproc(), lk);
   }
}


void
initsleeplock(struct sleeplock *lk, char *name)
{
  initlock(&lk->lk, "sleep lock");
  lk->name = name;
  lk->locked = 0;
  lk->pid = 0;
}

void
acquiresleep(struct sleeplock *lk)
{
  struct proc *p = myproc();
  struct proc *parent;
  acquire(&lk->lk);
  while (lk->locked) {
    if(p->waiting_for == 0) {
    //initial sleep
    //insert p(this is also a tree) to lk holder(parent). 
      parent = find_proc_with_pid(lk->pid);
      acquire(&tree_lock);
      insert_and_update(p, parent, lk);
      release(&tree_lock);
      p->waiting_for = lk;
    }
    sleep(lk, &lk->lk);
  }

  // now lk is available for p 
  lk->locked = 1;       
  lk->pid = p->pid;
  p->waiting_for = 0;

  // make orphans my children, who's waiting_for = lk    
  acquire(&tree_lock);
  collect_orphans(lk);
  release(&tree_lock);
  release(&lk->lk);
}


void
releasesleep(struct sleeplock *lk)
{
  

  acquire(&lk->lk);
  lk->locked = 0;
  lk->pid = 0;
  wakeup(lk);
  acquire(&tree_lock);
  remove_lk_children(lk);   // only lk value is referenced 
  release(&tree_lock);
  release(&lk->lk);


  // now refresh eprio, and if priority decreased, yield immediately.
  struct proc *p = myproc();
  int original_eprio;
  int new_eprio;
  acquire(&p->lock);
  original_eprio = p->eprio;
  release(&p->lock);
  new_eprio = refresh_eprio();
  if(new_eprio > original_eprio)
      kthread_yield();

}

int
holdingsleep(struct sleeplock *lk)
{
  int r;
  
  acquire(&lk->lk);
  r = lk->locked && (lk->pid == myproc()->pid);
  release(&lk->lk);
  return r;
}



