// Read write lock

region RWLock(r, x) {
  guards RLOCK1 * RUNLOCK1 * RLOCK2 * RUNLOCK2 * %WLOCK * WUNLOCK;
  interpretation {
    0 : x |-> 0 &*& r@(RUNLOCK1 * RUNLOCK2 * WUNLOCK);
    1 : x |-> 1 &*& r@(WUNLOCK * RUNLOCK2);
    2 : x |-> 1 &*& r@(WUNLOCK * RUNLOCK1);
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
  ensures RWLock(r, ret, 0) &*& r@(RLOCK1 * RLOCK2 * WLOCK[1p]);
{
    v := alloc(1);
    [v] := 0;
    return v;
}

function lockWriter(x)
  requires RWLock(r, x, _) &*& r@WLOCK[p];
  ensures RWLock(r, x, -1) &*& r@(WLOCK[p] * WUNLOCK);
{
    b := CAS(x, 0, -1);
    if (b = 0) {
        lockWriter(x);
    }
}

function unlockWriter(x)
  requires RWLock(r, x, -1) &*& r@WUNLOCK;
  ensures RWLock(r, x, _);
{
    [x] := 0;
}


function lockReader1(x)
  requires RWLock(r, x, m) &*& r@RLOCK1 &*& m != 1 &*& m != 3;
  ensures RWLock(r, x, n) &*& r@(RLOCK1 * RUNLOCK1) &*& n > 0;
{
    v := [x];
    if (v >= 0) {
        b := CAS(x, v, v + 1);
        if (b = 1) {
            return;
        }
    }
    lockReader1(x);
}


function unlockReader1(x)
  requires RWLock(r, x, n) &*& n > 0 &*& r@RUNLOCK1;
  ensures RWLock(r, x, _);
{
    v := [x];
    b := CAS(x, v, v - 1);
    if (b = 0) {
        unlockReader1(x);
    }
}

function lockReader2(x)
  requires RWLock(r, x, m) &*& r@RLOCK2 &*& m != 2 &*& m != 3;
  ensures RWLock(r, x, n) &*& r@(RLOCK2 * RUNLOCK2) &*& n > 0;
{
    v := [x];
    if (v >= 0) {
        b := CAS(x, v, v + 1);
        if (b = 1) {
            return;
        }
    }
    lockReader2(x);
}


function unlockReader2(x)
  requires RWLock(r, x, n) &*& n > 0 &*& r@RUNLOCK2;
  ensures RWLock(r, x, _);
{
    v := [x];
    b := CAS(x, v, v - 1);
    if (b = 0) {
        unlockReader2(x);
    }
}
