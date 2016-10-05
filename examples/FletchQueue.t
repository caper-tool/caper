#define HEAD(x) (x)
#define TAIL(x) (x + 1)

#define PREVIOUS(x) (x)
#define NEXT(x) (x + 1)
#define OWNER(x) (x + 2)

#define SENTINEL -1
#define NULL 0

#define TRYENQ_FAILED             0
#define TRYENQ_SUCCESS_EMPTY      1
#define TRYENQ_SUCCESS_NONEMPTY   2

#define TRYDEQ_FAILED             SENTINEL
#define TRYDEQ_SUCCESS_EMPTY      0

#define TRYDEQENTRY_FAILED        0
#define TRYDEQENTRY_SUCCESS       1

#define PROC(x,p,n) (PREVIOUS(x) |-> p &*& NEXT(x) |-> n)

region Process(r,x) {
  guards #OWNN * #OWNP * CONTROL;
  interpretation {
    NULL : (PROC(x,NULL,NULL) &*& r@(OWNN{z|true} * OWNP{z|true}) \/ r@(CONTROL)) &*& OWNER(x) |-> NULL;
    q != NULL | q : Queue(s,q,_) &*& OWNER(x) |-> q &*& (s@LK(x) \/ PROC(x,p,n) &*& r@(OWNP{z|z!=n} * OWNN{z|z!=p}) &*&
      (p = NULL ? s@HD(x) : Process(rp,p,q) &*& rp@OWNP(x)) &*&
      (n = NULL ? s@TL(x) : Process(rn,n,q) &*& rn@OWNN(x))) &*& r@CONTROL;
  }
  actions {
    OWNP{z|true} * OWNN{z|true} * CONTROL : q ~> q2;
  }
}


region Queue(s,q) {
  guards #HD * #TL * #LK;
  interpretation {
    0 : h != SENTINEL &*& HEAD(q) |-> h &*& TAIL(q) |-> t &*& s@LK{z|true} &*& 
        (h = NULL ? t = NULL &*& s@(HD{x|true} * TL{x|true}) :
        s@HD{x | x != h} &*& Process(r,h,q) &*& r@OWNN(NULL) &*&
        s@TL{x | x != t} &*& Process(r2,t,q) &*& r2@OWNP(NULL));
    1 : HEAD(q) |-> SENTINEL;
  }
  actions {
    : 0 ~> 1;
    LK{z|true} : 1 ~> 0;
  }
}
/*
function enqNE(queue,process)
  requires TAIL(queue) |-> tl &*& NEXT(tl) |-> _ &*& PREVIOUS(process) |-> _;
  ensures TAIL(queue) |-> process &*& NEXT(tl) |-> process &*& PREVIOUS(process) |-> tl;
{
    tail := [TAIL(queue)];
    [NEXT(tail)] := process;
    [PREVIOUS(process)] := tail;
    [TAIL(queue)] := process;
}

function enqE(queue,process)
  requires TAIL(queue) |-> _;
  ensures TAIL(queue) |-> process;
{
    [TAIL(queue)] := process;
}

function TryEnqueue(queue,process)
  requires Queue(s,queue,_) &*& Process(r,process,NULL) &*& r@CONTROL;
  ensures ret = TRYENQ_FAILED ? Process(r,process,NULL) &*& r@CONTROL : (ret = TRYENQ_SUCCESS_NONEMPTY \/ ret = TRYENQ_SUCCESS_EMPTY);
{
  h := TryLockHead(queue);
  if (h = SENTINEL) {
    return TRYENQ_FAILED;
  }
  else {
    [OWNER(process)] := queue;

  if (h != NULL) {
    enqNE(queue,process);
    [HEAD(queue)] := h;
    return TRYENQ_SUCCESS_NONEMPTY;
  } else {
    enqE(queue,process);
    [HEAD(queue)] := process;
    return TRYENQ_SUCCESS_EMPTY;
  }
  }
}
*/
function TryLockHead(queue)
  requires Queue(s,queue,_);
  ensures ret = SENTINEL ? true : Queue(s,queue,1) &*& queue != NULL &*&
     TAIL(queue) |-> t &*& s@LK{z|true} &*& 
        (ret = NULL ? t = NULL &*& s@(HD{x|true} * TL{x|true}) :
        s@HD{x | x != ret} &*& Process(r,ret,queue) &*& r@OWNN(NULL) &*&
        s@TL{x | x != t} &*& Process(r2,t,queue) &*& r2@OWNP(NULL));
{
  h := [HEAD(queue)];
  if (h != SENTINEL) {
    casRes := CAS(HEAD(queue),h,SENTINEL);
    if (casRes = 0) {
      h := TryLockHead(queue);
    }
  }
  return h;
}
/*
function TryDequeue(queue)
  requires Queue(s,queue,_);
  ensures ret = TRYDEQ_FAILED \/ ret = TRYDEQ_SUCCESS_EMPTY \/ (Process(r,ret,NULL) &*& r@CONTROL);
{
  h := TryLockHead(queue);
  if (h = SENTINEL) {
    return TRYDEQ_FAILED;
  } else {
    if (h = NULL) {
      return TRYDEQ_SUCCESS_EMPTY;
    } else {
      tail := [TAIL(queue)];
      if (tail = h) {
        [TAIL(queue)] := NULL;
      }
      next := [NEXT(h)];
      if (next != NULL) {
        [PREVIOUS(next)] := NULL;
      }
      // ChangeState(h,QUEUED,RUNNING);
      [OWNER(h)] := NULL;
      [NEXT(h)] := NULL;
      [HEAD(queue)] := next;
      return h;
    }
  }
}
*/
function TryDequeueEntry(queue,process)
  requires Queue(s,queue,_) &*& Process(r,process,_);
  ensures ret = TRYDEQENTRY_FAILED \/ ret = TRYDEQENTRY_SUCCESS &*& Process(r,process,NULL) &*& r@CONTROL;
{
  h := TryLockHead(queue);
  if (h = SENTINEL) {
    return TRYDEQENTRY_FAILED;
  }
  // At this point, the lock has been acquired
  owner := [OWNER(process)];
  if (owner != queue) {
    [HEAD(queue)] := h;
    return TRYDEQENTRY_FAILED;
  }
  // ChangeState(process,QUEUED,RUNNING);
  // At this point, process should not be reachable from other queues
  if (h = process) {
    // Dequeuing the head
    tail := [TAIL(queue)];
    if (h = tail) {
      [TAIL(queue)] := NULL;
    }
    h := [NEXT(h)];
  } else {
    next := [NEXT(process)];
    previous := [PREVIOUS(process)];
    [NEXT(previous)] := next;
    if (next = NULL) {
      [TAIL(queue)] := previous;
    } else {
      [PREVIOUS(next)] := previous;
    }
  }
  [OWNER(process)] := NULL;
  [NEXT(process)] := NULL;
  [HEAD(queue)] := h;
  return TRYDEQENTRY_SUCCESS;
}
