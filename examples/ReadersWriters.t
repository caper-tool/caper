region RWLock(r,x) {
  guards %WLOCK * WUNLOCK * %RLOCK * |RUNLOCK|;
  interpretation {
    0 : x |-> 0 &*& r@(WUNLOCK * RUNLOCK|-1|);
    1 : x |-> k &*& k > 0 &*& r@(WUNLOCK * RUNLOCK|-1-k|);
    2 : x |-> -1 &*& r@(RUNLOCK|-1|);
  }
  actions {
    WLOCK[_] : 0 ~> 2;
    WUNLOCK : 2 ~> 0;
    RLOCK[_] : 0 ~> 1;
    RUNLOCK|-1| : 1 ~> 0;
  }
}

function makeLock()
  requires true;
  ensures RWLock(r,ret,_) &*& r@(WLOCK[1p] * RLOCK[1p]);
{
  v := alloc(1);
  [v] := 0;
  return v;
}

function readerEntry(x)
  requires RWLock(r,x,_) &*& r@RLOCK[p];
  ensures  RWLock(r,x,1) &*& r@(RLOCK[p] * RUNLOCK|1|);
{
  v := [x];
  if (v >= 0) {
    b := CAS(x, v, v + 1);
    if (b != 0) {
      return;
    }
  }
  readerEntry(x);
}

function readerExit(x)
  requires RWLock(r,x,1) &*& r@UNLOCK|1|;
  ensures RWLock(r,x,_);
{
    v := [x];
    b := CAS(x, v, v - 1);
    if (b = 0) {
      readerExit(x);
    }
}

function writerEntry(x)
  requires RWLock(r,x,_) &*& r@WLOCK[p];
  ensures RWLock(r,x,2) &*& r@(WLOCK[p] * WUNLOCK);
{
  b := CAS(x, 0, -1);
  if (b = 0) {
    writerEntry(x);
  }
}

function writerExit(x)
  requires RWLock(r,x,2) &*& r@WUNLOCK;
  ensures RWLock(r,x,_);
{
  [x] := 0;
}
