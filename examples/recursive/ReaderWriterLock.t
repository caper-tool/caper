// Reader Write Lock

region RWLock(r,x) {
  guards WUNLOCK * |RUNLOCK|;
  interpretation {
    0 : x |-> 0 &*& r@(WUNLOCK * RUNLOCK|-1|);
    1 : x |-> k &*& k > 0 &*& r@(WUNLOCK * RUNLOCK|-1-k|);
    2 : x |-> -1 &*& r@(RUNLOCK|-1|);
  }
  actions {
    : 0 ~> 2;
    WUNLOCK : 2 ~> 0;
    : 0 ~> 1;
    RUNLOCK|-1| : 1 ~> 0;
  }
}

function makeLock()
  requires true;
  ensures RWLock(r,ret,_);
{
    v := alloc(1);
    [v] := 0;
    return v;
}

function readerAcquire(x)
  requires RWLock(r,x,_);
  ensures  RWLock(r,x,1) &*& r@(RUNLOCK|1|);
{
    v := [x];
    if (v >= 0) {
      b := CAS(x, v, v + 1);
      if (b != 0) {
        return;
      }
    }
    readerAcquire(x);
}

function readerRelease(x)
  requires RWLock(r,x,1) &*& r@RUNLOCK|1|;
  ensures RWLock(r,x,_);
{
    v := [x];
    assert v = 1 ? true : true;
    b := CAS(x, v, v - 1);
    if (b = 0) {
      readerRelease(x);
    }
}

function writerAcquire(x)
  requires RWLock(r,x,_);
  ensures RWLock(r,x,2) &*& r@WUNLOCK;
{
    b := CAS(x, 0, -1);
    if (b = 0) {
      writerAcquire(x);
    }
}

function writerRelease(x)
  requires RWLock(r,x,2) &*& r@WUNLOCK;
  ensures RWLock(r,x,_);
{
    [x] := 0;
}
