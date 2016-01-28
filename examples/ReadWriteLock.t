// Read write lock

region RWLock(r, x) {
  guards RLOCK1 * RUNLOCK1 * RLOCK2 * RUNLOCK2 * %WLOCK * WUNLOCK;
  interpretation {
    0 : x |-> 0 &*& r@(RUNLOCK1 * RUNLOCK2 * WUNLOCK);
    1 : x |-> 1 &*& r@(WUNLOCK * RUNLOCK1);
    2 : x |-> 1 &*& r@(WUNLOCK * RUNLOCK2);
    3 : x |-> 2 &*& r@(WUNLOCK);
    -1 : x |-> -1 &*& r@(RUNLOCK1 * RUNLOCK2);
  }
  actions {
    RLOCK1 : 0 ~> 1;
    RUNLOCK1 : 1 ~> 0;
    RLOCK2 : 0 ~> 2;
    RUNLOCK2 : 2 ~> 0;
    RLOCK1 : 2 ~> 3;
    RUNLOCK1 : 3 ~> 2;
    RLOCK2 : 1 ~> 3;
    RUNLOCK2 : 3 ~> 1;
    WLOCK[_] : 0 ~> -1;
    WUNLOCK : -1 ~> 0;
  }
}

function makeLock()
  requires true;
  ensures RWLock(r, ret, n) &*& n >= -1;
{
    v := alloc(1);
    [v] := 0;
    return v;
}
/*
&*& r@(RLOCK1 * RLOCK2 * WLOCK[1p]) &*& n >= -1
function lock(x)
  requires SLock(r,x,_) &*& r@(LOCK[p]);
  ensures SLock(r,x,1) &*& r@(LOCK[p] * UNLOCK); {
    do
        invariant b = 0 ? SLock(r,x,_) &*& r@(LOCK[p]) : SLock(r,x,1) &*& r@(LOCK[p] * UNLOCK)
    {
        b := CAS(x, 0, 1);
    } while (b = 0);
}

function unlock(x)
  requires SLock(r,x,1) &*& r@(UNLOCK);
  ensures SLock(r,x,_); {
    [x] := 0;
}
*/