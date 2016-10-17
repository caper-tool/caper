// Ticket Lock

region TLock(r,x) {
  guards #NEXT;
  interpretation {
    n : x |-> m &*& (x + 1) |-> n &*& r@NEXT{ k | k >= m } &*& m >= n;
  }
  actions {
    n < m | NEXT{ k | n <= k, k < m } : n ~> m;
  }
}

function makeLock()
  requires true;
  ensures TLock(r,ret,_);
{
    v := alloc(2);
    [v + 0] := 0;
    [v + 1] := 0;
    return v;
}

function acquire(x)
  requires TLock(r,x,_);
  ensures TLock(r,x,n) &*& r@NEXT(n);
{
    do {
        t := [x + 0];
        b := CAS(x + 0, t, t + 1);
    }
      invariant TLock(r,x,ni) &*& (b = 0 ? true : r@NEXT(t) &*& t >= ni);
    while (b = 0);
    do {
        v := [x + 1];
    }
      invariant TLock(r,x,ni) &*& r@NEXT(t) &*& t >= ni &*& ni >= v;
    while (v < t);
}

function release(x)
  requires TLock(r,x,n) &*& r@NEXT(n);
  ensures TLock(r,x,_);
{
    v := [x + 1];
    [x + 1] := v + 1;
}
