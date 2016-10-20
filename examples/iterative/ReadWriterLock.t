// Read Write Lock

region RWLock(r,x) {
  guards WUNLOCK * |RUNLOCK|;
  interpretation {
    0 : x |-> 0 &*& r@(WUNLOCK * RUNLOCK|-1|);
    1 : x |-> k &*& k > 0 &*& r@(WUNLOCK * RUNLOCK|-1-k|);
    2 : x |-> -1 &*& r@RUNLOCK|-1|;
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
  ensures  RWLock(r,x,1) &*& r@RUNLOCK|1|;
{
    do {
        v := [x];
        if (v >= 0) {
            b := CAS(x, v, v + 1);
        } else {
            b := 0;
        }
    }
      invariant RWLock(r,x,ni) &*& (b = 0 ? true : ni = 1 &*& r@RUNLOCK|1|);
    while (b = 0);
}

function readerRelease(x)
  requires RWLock(r,x,1) &*& r@RUNLOCK|1|;
  ensures RWLock(r,x,_);
{
    do {
        v := [x];
        assert v = 1 ? true : true;
        b := CAS(x, v, v - 1);
    }
      invariant RWLock(r,x,ni) &*& (b = 0 ? ni = 1 &*& r@RUNLOCK|1| : true);
    while (b = 0);
}

function writerAcquire(x)
  requires RWLock(r,x,_);
  ensures RWLock(r,x,2) &*& r@WUNLOCK;
{
    do {
        b := CAS(x, 0, -1);
    }
      invariant b = 0 ? RWLock(r,x,_) : RWLock(r,x,2) &*& r@WUNLOCK;
    while (b = 0);
}

function writerRelease(x)
  requires RWLock(r,x,2) &*& r@WUNLOCK;
  ensures RWLock(r,x,_);
{
    [x] := 0;
}
