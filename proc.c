#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"

int total_runnable_weight = 0;


void left_rotate(struct rbt_tree *tree, struct rbt_node *x) {
    struct rbt_node *y = x->right;
    x->right = y->left;
    if (y->left != NULL) {
        y->left->parent = x;
    }
    y->parent = x->parent;
    if (x->parent == NULL) {
        tree->root = y;
    } else if (x == x->parent->left) {
        x->parent->left = y;
    } else {
        x->parent->right = y;
    }
    y->left = x;
    x->parent = y;
}

void right_rotate(struct rbt_tree *tree, struct rbt_node *y) {
    struct rbt_node *x = y->left;
    y->left = x->right;
    if (x->right != NULL) {
        x->right->parent = y;
    }
    x->parent = y->parent;
    if (y->parent == NULL) {
        tree->root = x;
    } else if (y == y->parent->right) {
        y->parent->right = x;
    } else {
        y->parent->left = x;
    }
    x->right = y;
    y->parent = x;
}

void insert_fixup(struct rbt_tree *tree, struct rbt_node *z) {
    while (z->parent && z->parent->color == RED) {
        if (z->parent == z->parent->parent->left) {
            struct rbt_node *y = z->parent->parent->right;
            if (y && y->color == RED) {
                z->parent->color = BLACK;
                y->color = BLACK;
                z->parent->parent->color = RED;
                z = z->parent->parent;
            } else {
                if (z == z->parent->right) {
                    z = z->parent;
                    left_rotate(tree, z);
                }
                z->parent->color = BLACK;
                z->parent->parent->color = RED;
                right_rotate(tree, z->parent->parent);
            }
        } else {
            // Symmetric to the above case, left and right swapped
            struct rbt_node *y = z->parent->parent->left;
            if (y && y->color == RED) {
                z->parent->color = BLACK;
                y->color = BLACK;
                z->parent->parent->color = RED;
                z = z->parent->parent;
            } else {
                if (z == z->parent->left) {
                    z = z->parent;
                    right_rotate(tree, z);
                }
                z->parent->color = BLACK;
                z->parent->parent->color = RED;
                left_rotate(tree, z->parent->parent);
            }
        }
    }
    tree->root->color = BLACK;
}

void insert_rbt(struct rbt_tree *tree, struct proc *p) {
    struct rbt_node *z = (struct rbt_node *)kalloc(); // Assume kalloc() allocates kernel memory
    z->proc = p;
    struct rbt_node *y = NULL;
    struct rbt_node *x = tree->root;

    // Standard BST insertion
    while (x != NULL) {
        y = x;
        if (p->vruntime < x->proc->vruntime) {
            x = x->left;
        } else {
            x = x->right;
        }
    }
    z->parent = y;
    if (y == NULL) {
        tree->root = z;
    } else if (p->vruntime < y->proc->vruntime) {
        y->left = z;
    } else {
        y->right = z;
    }

    // Set node properties and insert node into tree
    z->left = NULL;
    z->right = NULL;
    z->color = RED;

    // Fix RBT properties
    insert_fixup(tree, z);
}

struct rbt_node* tree_minimum(struct rbt_node *x) {
    while (x->left != NULL) {
        x = x->left;
    }
    return x;
}

void delete_fixup(struct rbt_tree *tree, struct rbt_node *x) {
    while (x != tree->root && x->color == BLACK) {
        if (x == x->parent->left) {
            struct rbt_node *w = x->parent->right;
            if (w->color == RED) {
                w->color = BLACK;
                x->parent->color = RED;
                left_rotate(tree, x->parent);
                w = x->parent->right;
            }
            if (w->left->color == BLACK && w->right->color == BLACK) {
                w->color = RED;
                x = x->parent;
            } else {
                if (w->right->color == BLACK) {
                    w->left->color = BLACK;
                    w->color = RED;
                    right_rotate(tree, w);
                    w = x->parent->right;
                }
                w->color = x->parent->color;
                x->parent->color = BLACK;
                w->right->color = BLACK;
                left_rotate(tree, x->parent);
                x = tree->root;
            }
        } else {
            // Symmetric to the above case, left and right swapped
            struct rbt_node *w = x->parent->left;
            if (w->color == RED) {
                w->color = BLACK;
                x->parent->color = RED;
                right_rotate(tree, x->parent);
                w = x->parent->left;
            }
            if (w->right->color == BLACK && w->right->color == BLACK) {
                w->color = RED;
                x = x->parent;
            } else {
                if (w->left->color == BLACK) {
                    w->right->color = BLACK;
                    w->color = RED;
                    left_rotate(tree, w);
                    w = x->parent->left;
                }
                w->color = x->parent->color;
                x->parent->color = BLACK;
                w->left->color = BLACK;
                right_rotate(tree, x->parent);
                x = tree->root;
            }
        }
    }
    x->color = BLACK;
}

void delete_rbt(struct rbt_tree *tree, struct proc *p) {
    struct rbt_node *z = NULL;
    struct rbt_node *x, *y;

    // Find the node z in the tree that corresponds to process p
    for (z = tree->root; z != NULL; z = (p->vruntime < z->proc->vruntime) ? z->left : z->right) {
        if (z->proc == p) {
            break;
        }
    }

    if (!z || z->proc != p) {
        return; // Process not found in the tree
    }

    if (z->left == NULL || z->right == NULL) {
        y = z;
    } else {
        y = tree_minimum(z->right);
    }

    if (y->left != NULL) {
        x = y->left;
    } else {
        x = y->right;
    }

    if (x != NULL) {
        x->parent = y->parent;
    }

    if (y->parent == NULL) {
        tree->root = x;
    } else if (y == y->parent->left) {
        y->parent->left = x;
    } else {
        y->parent->right = x;
    }

    if (y != z) {
        z->proc = y->proc;
    }

    if (y->color == BLACK) {
        delete_fixup(tree, x);
    }

    kfree((char*)y);
}

struct proc* find_min_vruntime(struct rbt_tree *tree) {
    struct rbt_node *x = tree->root;
    if (!x) {
        return NULL; // Tree is empty
    }

    // Traverse to the leftmost node
    while (x->left != NULL) {
        x = x->left;
    }

    // Return the process with minimum vruntime
    return x->proc;
}

struct proc* find_next_vruntime(struct rbt_tree *tree, int vruntime) {
    struct rbt_node *x = tree->root;
    struct rbt_node *next = NULL;

    while (x != NULL) {
        if (x->proc->vruntime > vruntime) {
            next = x;
            x = x->left;
        } else {
            x = x->right;
        }
    }

    return next ? next->proc : NULL;
}

int NICE_WEIGHTS[40] = {
/*  0 */   88761,  71755,  56483,  46273,  36291,
/*  5 */   29154,  23254,  18705,  14949,  11916,
/* 10 */   9548,   7620,   6100,   4904,   3906,
/* 15 */   3121,   2501,   1991,   1586,   1277,
/* 20 */   1024,   820,    655,    526,    423,
/* 25 */   335,    272,    215,    172,    137,
/* 30 */   110,    87,     70,     56,     45,
/* 35 */   36,     29,     23,     18,     15
};

struct {
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

static struct proc *initproc;
struct rbt_tree rbt_tree;

int nextpid = 1;
extern void forkret(void);
extern void trapret(void);

int min_vruntime(void) {
  struct proc *p;
  int min_vr = 0x7FFFFFFF;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
    if(p->state == RUNNABLE && p->vruntime < min_vr) {
      min_vr = p->vruntime;
    }
  }
  release(&ptable.lock);

  if(min_vr == 0x7FFFFFFF) {
    return 0;
  } else {
    return min_vr;
  }
}

void update_total_runnable_weight(struct proc *p, int old_state) {
  acquire(&ptable.lock);
  if (old_state != RUNNABLE && p->state == RUNNABLE) {
    total_runnable_weight += p->weight;
  } else if (old_state == RUNNABLE && p->state != RUNNABLE) {
    total_runnable_weight -= p->weight;
  }
  release(&ptable.lock);
}

int calculate_time_slice(struct proc *p) {
  acquire(&ptable.lock);
  int time_slice = (total_runnable_weight == 0) ? 10 : (10 * p->weight) / total_runnable_weight;
  release(&ptable.lock);
  return time_slice;
}

static void wakeup1(void *chan);


void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
}

// Must be called with interrupts disabled
int
cpuid() {
  return mycpu()-cpus;
}

// Must be called with interrupts disabled to avoid the caller being
// rescheduled between reading lapicid and running through the loop.
struct cpu*
mycpu(void)
{
  int apicid, i;
  
  if(readeflags()&FL_IF)
    panic("mycpu called with interrupts enabled\n");
  
  apicid = lapicid();
  // APIC IDs are not guaranteed to be contiguous. Maybe we should have
  // a reverse map, or reserve a register to store &cpus[i].
  for (i = 0; i < ncpu; ++i) {
    if (cpus[i].apicid == apicid)
      return &cpus[i];
  }
  panic("unknown apicid\n");
}

// Disable interrupts so that we are not rescheduled
// while reading proc from the cpu structure
struct proc*
myproc(void) {
  struct cpu *c;
  struct proc *p;
  pushcli();
  c = mycpu();
  p = c->proc;
  popcli();
  return p;
}

//PAGEBREAK: 32
// Look in the process table for an UNUSED proc.
// If found, change state to EMBRYO and initialize
// state required to run in the kernel.
// Otherwise return 0.
static struct proc*
allocproc(void)
{
  struct proc *p;
  char *sp;

  acquire(&ptable.lock);

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == UNUSED)
      goto found;

  release(&ptable.lock);
  return 0;

found:
  p->state = EMBRYO;
  p->pid = nextpid++;

  p->nice = DEFAULT_NICE;
  p->vruntime = 0;
  p->actual_runtime = 0;
  p->weight = NICE_WEIGHTS[20];

  release(&ptable.lock);

  // Allocate kernel stack.
  if((p->kstack = kalloc()) == 0){
    p->state = UNUSED;
    return 0;
  }
  sp = p->kstack + KSTACKSIZE;

  // Leave room for trap frame.
  sp -= sizeof *p->tf;
  p->tf = (struct trapframe*)sp;

  // Set up new context to start executing at forkret,
  // which returns to trapret.
  sp -= 4;
  *(uint*)sp = (uint)trapret;

  sp -= sizeof *p->context;
  p->context = (struct context*)sp;
  memset(p->context, 0, sizeof *p->context);
  p->context->eip = (uint)forkret;

  return p;
}

//PAGEBREAK: 32
// Set up first user process.
void
userinit(void)
{
  struct proc *p;
  extern char _binary_initcode_start[], _binary_initcode_size[];

  p = allocproc();
  
  initproc = p;
  if((p->pgdir = setupkvm()) == 0)
    panic("userinit: out of memory?");
  inituvm(p->pgdir, _binary_initcode_start, (int)_binary_initcode_size);
  p->sz = PGSIZE;
  memset(p->tf, 0, sizeof(*p->tf));
  p->tf->cs = (SEG_UCODE << 3) | DPL_USER;
  p->tf->ds = (SEG_UDATA << 3) | DPL_USER;
  p->tf->es = p->tf->ds;
  p->tf->ss = p->tf->ds;
  p->tf->eflags = FL_IF;
  p->tf->esp = PGSIZE;
  p->tf->eip = 0;  // beginning of initcode.S

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  // this assignment to p->state lets other cores
  // run this process. the acquire forces the above
  // writes to be visible, and the lock is also needed
  // because the assignment might not be atomic.
  acquire(&ptable.lock);

  p->state = RUNNABLE;

  release(&ptable.lock);
}

// Grow current process's memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  uint sz;
  struct proc *curproc = myproc();

  sz = curproc->sz;
  if(n > 0){
    if((sz = allocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  } else if(n < 0){
    if((sz = deallocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  }
  curproc->sz = sz;
  switchuvm(curproc);
  return 0;
}

// Create a new process copying p as the parent.
// Sets up stack to return as if from system call.
// Caller must set state of returned proc to RUNNABLE.
int
fork(void)
{
  int i, pid;
  struct proc *np;
  struct proc *curproc = myproc();

  // Allocate process.
  if((np = allocproc()) == 0){
    return -1;
  }

  // Copy process state from proc.
  if((np->pgdir = copyuvm(curproc->pgdir, curproc->sz)) == 0){
    kfree(np->kstack);
    np->kstack = 0;
    np->state = UNUSED;
    return -1;
  }
  np->sz = curproc->sz;
  np->parent = curproc;
  *np->tf = *curproc->tf;

  // Clear %eax so that fork returns 0 in the child.
  np->tf->eax = 0;

  for(i = 0; i < NOFILE; i++)
    if(curproc->ofile[i])
      np->ofile[i] = filedup(curproc->ofile[i]);
  np->cwd = idup(curproc->cwd);

  safestrcpy(np->name, curproc->name, sizeof(curproc->name));

  pid = np->pid;

  acquire(&ptable.lock);

  insert_rbt(&rbt_tree, np);

  np->state = RUNNABLE;
  update_total_runnable_weight(np, UNUSED);
  np->vruntime = curproc->vruntime;

  release(&ptable.lock);

  return pid;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait() to find out it exited.
void
exit(void)
{
  struct proc *curproc = myproc();
  struct proc *p;
  int fd;

  if(curproc == initproc)
    panic("init exiting");

  // Close all open files.
  for(fd = 0; fd < NOFILE; fd++){
    if(curproc->ofile[fd]){
      fileclose(curproc->ofile[fd]);
      curproc->ofile[fd] = 0;
    }
  }

  begin_op();
  iput(curproc->cwd);
  end_op();
  curproc->cwd = 0;

  acquire(&ptable.lock);

  // Parent might be sleeping in wait().
  wakeup1(curproc->parent);

  // Pass abandoned children to init.
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->parent == curproc){
      p->parent = initproc;
      if(p->state == ZOMBIE)
        wakeup1(initproc);
    }
  }

  delete_rbt(&rbt_tree, curproc);

  // Jump into the scheduler, never to return.
  curproc->state = ZOMBIE;
  update_total_runnable_weight(myproc(), RUNNING);

  sched();
  panic("zombie exit");
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(void)
{
  struct proc *p;
  int havekids, pid;
  struct proc *curproc = myproc();
  
  acquire(&ptable.lock);
  for(;;){
    // Scan through table looking for exited children.
    havekids = 0;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->parent != curproc)
        continue;
      havekids = 1;
      if(p->state == ZOMBIE){
        // Found one.
        pid = p->pid;
        kfree(p->kstack);
        p->kstack = 0;
        freevm(p->pgdir);
        p->pid = 0;
        p->parent = 0;
        p->name[0] = 0;
        p->killed = 0;
        p->state = UNUSED;
        release(&ptable.lock);
        return pid;
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || curproc->killed){
      release(&ptable.lock);
      return -1;
    }

    // Wait for children to exit.  (See wakeup1 call in proc_exit.)
    sleep(curproc, &ptable.lock);  //DOC: wait-sleep
  }
}

//PAGEBREAK: 42
// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run
//  - swtch to start running that process
//  - eventually that process transfers control
//      via swtch back to the scheduler.
void
scheduler(void)
{
  struct proc *p;
  struct cpu *c = mycpu();
  c->proc = 0;
  
  for(;;){
    // Enable interrupts on this processor.
    sti();

    // Loop over process table looking for process to run.
    acquire(&ptable.lock);

     p = find_min_vruntime(&rbt_tree);

    while(p != NULL) {
      if(p->state != RUNNABLE) {
        // Process is not runnable, find the next process in the RBT
        p = find_next_vruntime(&rbt_tree, p->vruntime);
        continue;
      }

      // Switch to chosen process. It is the process's job
      // to release ptable.lock and then reacquire it
      // before jumping back to us.
      c->proc = p;
      switchuvm(p);
      p->state = RUNNING;

      swtch(&(c->scheduler), p->context);
      switchkvm();

      // Process is done running for now.
      // It should have changed its p->state before coming back.
      c->proc = 0;

      if(p->yield_flag) {
        // Move to the next process in the red-black tree
        p = find_next_vruntime(&rbt_tree, p->vruntime);
        p->yield_flag = 0;
      } else {
        // If the process hasn't yielded, break the loop and
        // let it continue running.
        break;
      }
    }
    
    release(&ptable.lock);

  }
}

// Enter scheduler.  Must hold only ptable.lock
// and have changed proc->state. Saves and restores
// intena because intena is a property of this
// kernel thread, not this CPU. It should
// be proc->intena and proc->ncli, but that would
// break in the few places where a lock is held but
// there's no process.
void
sched(void)
{
  int intena;
  struct proc *p = myproc();

  if(!holding(&ptable.lock))
    panic("sched ptable.lock");
  if(mycpu()->ncli != 1)
    panic("sched locks");
  if(p->state == RUNNING)
    panic("sched running");
  if(readeflags()&FL_IF)
    panic("sched interruptible");
  intena = mycpu()->intena;
  swtch(&p->context, mycpu()->scheduler);
  mycpu()->intena = intena;
}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  acquire(&ptable.lock);  //DOC: yieldlock
  myproc()->state = RUNNABLE;
  update_total_runnable_weight(myproc(), RUNNING);
  sched();
  release(&ptable.lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch here.  "Return" to user space.
void
forkret(void)
{
  static int first = 1;
  // Still holding ptable.lock from scheduler.
  release(&ptable.lock);

  if (first) {
    // Some initialization functions must be run in the context
    // of a regular process (e.g., they call sleep), and thus cannot
    // be run from main().
    first = 0;
    iinit(ROOTDEV);
    initlog(ROOTDEV);
  }

  // Return to "caller", actually trapret (see allocproc).
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  struct proc *p = myproc();
  
  if(p == 0)
    panic("sleep");

  if(lk == 0)
    panic("sleep without lk");

  // Must acquire ptable.lock in order to
  // change p->state and then call sched.
  // Once we hold ptable.lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup runs with ptable.lock locked),
  // so it's okay to release lk.
  if(lk != &ptable.lock){  //DOC: sleeplock0
    acquire(&ptable.lock);  //DOC: sleeplock1
    release(lk);
  }
  // Go to sleep.
  p->chan = chan;
  p->state = SLEEPING;

  sched();

  // Tidy up.
  p->chan = 0;

  // Reacquire original lock.
  if(lk != &ptable.lock){  //DOC: sleeplock2
    release(&ptable.lock);
    acquire(lk);
  }
}

//PAGEBREAK!
// Wake up all processes sleeping on chan.
// The ptable lock must be held.
static void
wakeup1(void *chan)
{
  struct proc *p;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == SLEEPING && p->chan == chan) {
      p->state = RUNNABLE;
      update_total_runnable_weight(myproc(), SLEEPING);

      int vruntime_1tick = (1 * NICE_WEIGHTS[20]) / p->weight;
      p->vruntime = min_vruntime() - vruntime_1tick;
    }
}

// Wake up all processes sleeping on chan.
void
wakeup(void *chan)
{
  acquire(&ptable.lock);
  wakeup1(chan);
  release(&ptable.lock);
}

// Kill the process with the given pid.
// Process won't exit until it returns
// to user space (see trap in trap.c).
int
kill(int pid)
{
  struct proc *p;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == pid){
      p->killed = 1;
      // Wake process from sleep if necessary.
      if(p->state == SLEEPING)
        p->state = RUNNABLE;
      release(&ptable.lock);
      return 0;
    }
  }
  release(&ptable.lock);
  return -1;
}

//PAGEBREAK: 36
// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [EMBRYO]    "embryo",
  [SLEEPING]  "sleep ",
  [RUNNABLE]  "runble",
  [RUNNING]   "run   ",
  [ZOMBIE]    "zombie"
  };
  int i;
  struct proc *p;
  char *state;
  uint pc[10];

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    cprintf("%d %s %s", p->pid, state, p->name);
    if(p->state == SLEEPING){
      getcallerpcs((uint*)p->context->ebp+2, pc);
      for(i=0; i<10 && pc[i] != 0; i++)
        cprintf(" %p", pc[i]);
    }
    cprintf("\n");
  }
}


int
getpname(int pid)
{
  struct proc *p;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
    if(p -> pid == pid) {
      cprintf("%s\n", p->name);
      release(&ptable.lock);
      return 0;
    }
  }
  release(&ptable.lock);
  return -1;
}

int
getnice(int pid)
{
  struct proc *p;
  int nice_value = -1;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
    if(p -> pid == pid) {
      nice_value = p->nice;
      break;
    }
  }

  release(&ptable.lock);
  return nice_value;
}

int
setnice(int pid, int value)
{
  struct proc *p;

  if(value < MIN_NICE || value > MAX_NICE) {
    return -1;
  }

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
    if(p -> pid == pid) {
      p->nice = value;
      release(&ptable.lock);
      
      return 0;
    }
  }

  release(&ptable.lock);
  return -1;
}

void
ps(int pid)
{
  struct proc *p;
  struct proc proc_array[NPROC] = {0};

  char* procstate_strings[] = {
    "UNUSED",
    "EMBRYO",
    "SLEEPING",
    "RUNNABLE",
    "RUNNING",
    "ZOMBIE"
  };

  int proc_found = 0;

  acquire(&ptable.lock);

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
    if(p->pid == pid || pid == 0) {
      if(p->state == UNUSED) {
        continue;
      }

      proc_array[p->pid].pid = p->pid;
      proc_array[p->pid].state = p->state;
      proc_array[p->pid].nice = p->nice;
      safestrcpy(proc_array[p->pid].name, p->name, sizeof(p->name));

      proc_found = 1;
    }
  }

  release(&ptable.lock);

  
  if(proc_found) {
    cprintf("name\tpid\t\tstate\t\tpriority\n");

    for(p = proc_array; p < &proc_array[NPROC]; p++) {
      if(p->pid != 0)   {
        cprintf("%s\t%d\t\t%s\t\t%d\n", p->name, p->pid, procstate_strings[p->state], p->nice);
      }
    }
  }

  return;
}