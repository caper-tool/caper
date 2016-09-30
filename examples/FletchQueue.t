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

#define PROC(x,p,n,o) (PREVIOUS(x) |-> p &*& NEXT(x) |-> n &*& OWNER(x) |-> o)

region Process(r,x) {
  guards #OWNN * #OWNP * CONTROL;
  interpretation {
    NULL : PROC(x,NULL,NULL,NULL) &*& r@(OWNN{z|true} * OWNP{z|true}) \/ r@(CONTROL);
    q != NULL | q : (PROC(x,p,n,q) \/ s@LK(x)) &*& r@(OWNP{z|z!=n} * OWNN{z|z!=p}) &*& Queue(s,q,_) &*&
      (p = NULL ? s@HD(x) : Process(rp,p,q) &*& rp@OWNP(x)) &*&
      (n = NULL ? s@TL(x) : Process(rn,n,q) &*& rn@OWNN(x)) &*& r@CONTROL;
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

/*
function enqE2(queue,process)
  requires TAIL(queue) |-> process &*& s@(LK{z|true} * HD{x|x!=process} * TL{x|x!=process}) &*& r@(OWNN(NULL) * OWNP(NULL)) &*& Process(r,process,0) &*&
      PROC(process,NULL,NULL,queue) &*& r@(OWNP{z|z!=NULL} * OWNN{z|z!=NULL}) &*& s@(HD(process) * TL(process)) &*& Queue(s,queue,_);
  ensures true;
{
    [HEAD(queue)] := process; 
}
*/


function TryEnqueue(queue,process)
requires false;
//  requires Queue(s,queue,_) &*& Process(r,process,NULL) &*& r@CONTROL;
  ensures true;
{
  h := TryLockHead(queue);
  if (h = SENTINEL) {
    return TRYENQ_FAILED;
  }
  else {
    [OWNER(process)] := queue;
  }
  
  if (h != NULL) {
    enqNE(queue,process);
    [HEAD(queue)] := h;
    return TRYENQ_SUCCESS_NONEMPTY;
  } else {
    enqE(queue,process);
/*    assert TAIL(queue) |-> process &*& s@(LK{z|true} * HD{x|x!=process} * TL{x|x!=process}) &*& r@(OWNN(NULL) * OWNP(NULL)) &*& Process(r,process,0) &*&
      PROC(x,NULL,NULL,queue) &*& r@(OWNP{z|z!=NULL} * OWNN{z|z!=NULL}) &*& s@(HD(process) * TL(process)) &*& Queue(s,queue,_);*/
    [HEAD(queue)] := process;
    return TRYENQ_SUCCESS_EMPTY;
  }
}

function TryLockHead(queue)
  requires Queue(s,queue,_);
  ensures ret = SENTINEL ? true : Queue(s,queue,1) &*& 
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

function TryDequeue(queue)
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

function TryDequeueEntry(queue,process)
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
