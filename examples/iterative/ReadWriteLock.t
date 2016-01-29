// Read Write Lock

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
    do
      invariant r@WLOCK[p] &*& (b = 0 ? RWLock(r, x, _) : RWLock(r, x, -1) &*& r@WUNLOCK)
    {
        b := CAS(x, 0, -1);
    } while (b = 0);
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
    do
      invariant RWLock(r, x, mi) &*& r@RLOCK1 &*& (b = 0 ? mi != 1 &*& mi != 3 : mi > 0 &*& r@RUNLOCK1)
    {
        v := [x];
        if (v >= 0) {
            b := CAS(x, v, v + 1);
        } else {
            b := 0;
        }
    } while (b = 0);
}

function unlockReader1(x)
  requires RWLock(r, x, n) &*& n > 0 &*& r@RUNLOCK1;
  ensures RWLock(r, x, _);
{
    do
      invariant RWLock(r, x, ni) &*& (b = 0 ? ni > 0 &*& r@RUNLOCK1 : true)
    {
        v := [x];
        b := CAS(x, v, v - 1);
    } while (b = 0);
}

function lockReader2(x)
  requires RWLock(r, x, m) &*& r@RLOCK2 &*& m != 2 &*& m != 3;
  ensures RWLock(r, x, n) &*& r@(RLOCK2 * RUNLOCK2) &*& n > 0;
{
    do
      invariant RWLock(r, x, mi) &*& r@RLOCK2 &*& (b = 0 ? mi != 2 &*& mi != 3 : mi > 0 &*& r@RUNLOCK2)
    {
        v := [x];
        if (v >= 0) {
            b := CAS(x, v, v + 1);
        } else {
            b := 0;
        }
    } while (b = 0);
}

function unlockReader2(x)
  requires RWLock(r, x, n) &*& n > 0 &*& r@RUNLOCK2;
  ensures RWLock(r, x, _);
{
    do
      invariant RWLock(r, x, ni) &*& (b = 0 ? ni > 0 &*& r@RUNLOCK2 : true)
    {
        v := [x];
        b := CAS(x, v, v - 1);
    } while (b = 0);
}
