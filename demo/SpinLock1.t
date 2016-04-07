// Spin Lock

region SLock(r, x) {
  guards UNLOCK;
  interpretation {
    0 : x |-> 0 &*& r@UNLOCK;
    1 : x |-> 1;
  }
  actions {
           : 0 ~> 1;
    UNLOCK : 1 ~> 0;
  }
}


function makeLock()
  requires true;
  ensures SLock(r, ret, _);
{
    v := alloc(1);
    [v] := 0;
    return v;
}


function lock(x)
  requires SLock(r, x, _);
  ensures SLock(r, x, 1) &*& r@UNLOCK;
{
    do {
        b := CAS(x, 0, 1);
    }
      invariant b = 0 ? SLock(r,x,_) : SLock(r, x, 1) &*& r@UNLOCK;
    while (b = 0);
}

function unlock(x)
  requires SLock(r, x, 1) &*& r@UNLOCK;
  ensures SLock(r, x, _);
{
    [x] := 0;
}
