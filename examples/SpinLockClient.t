// Spin Lock Client

region SLock(r,x) {
  guards %LOCK * UNLOCK;
  interpretation {
    0 : x |-> 0 &*& r@UNLOCK;
    1 : x |-> 1;
  }
  actions {
    LOCK[_] : 0 ~> 1;
    UNLOCK : 1 ~> 0;
  }
}
/*
function makeLock()
  requires true;
  ensures SLock(r,ret,0) &*& r@LOCK[1p];
{
    v := alloc(1);
    [v] := 0;
    return v;
}
*/
function acquire(x)
  requires SLock(r,x,_) &*& r@LOCK[p];
  ensures SLock(r,x,1) &*& r@(LOCK[p] * UNLOCK);
{
    do {
        b := CAS(x, 0, 1);
    }
      invariant b = 0 ? SLock(r,x,_) &*& r@LOCK[p] : SLock(r, x, 1) &*& r@(LOCK[p] * UNLOCK);
    while (b = 0);
}

function release(x)
  requires SLock(r,x,1) &*& r@UNLOCK;
  ensures SLock(r,x,_);
{
    [x] := 0;
}

region Client(r,x,s,z) {
  guards 0;
  interpretation {
    0 : SLock(s,z,k) &*& s@LOCK[p] &*& (x |-> a &*& (x+1) |-> a \/ s@UNLOCK);
  }
  actions {
  }
}

function foo(x, z, w)
  requires Client(r,x,s,z,0);
  ensures Client(r,x,s,z,0);
{
  skip;
  acquire(z);
  t := [x];
  [x] := w;
  [x + 1] := w;
  release(z);
}
