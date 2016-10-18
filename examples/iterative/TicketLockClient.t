// Ticket Lock

region TLock(r,x) {
  guards #TICKET;
  interpretation {
    n : x |-> m &*& (x + 1) |-> n &*& r@TICKET{ k | k >= m } &*& m >= n;
  }
  actions {
    n < m | TICKET{ k | n <= k, k < m } : n ~> m;
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
  ensures TLock(r,x,n) &*& r@TICKET(n);
{
    do {
        t := [x + 0];
        b := CAS(x + 0, t, t + 1);
    }
      invariant TLock(r,x,ni) &*& (b = 0 ? true : r@TICKET(t) &*& t >= ni);
    while (b = 0);
    do {
        v := [x + 1];
    }
      invariant TLock(r,x,ni) &*& r@TICKET(t) &*& t >= ni &*& ni >= v;
    while (v < t);
}

function release(x)
  requires TLock(r,x,n) &*& r@TICKET(n);
  ensures TLock(r,x,_);
{
    v := [x + 1];
    [x + 1] := v + 1;
}

region Client(r,x,s,z) {
  guards 0;
  interpretation {
    0 : TLock(s,z,k) &*& (x |-> a &*& (x+1) |-> a \/ s@TICKET(k));
  }
  actions {
  }
}

function foo(x, z, w)
  requires Client(r,x,s,z,0) &*& TLock(s,z,_);
  ensures Client(r,x,s,z,0) &*& TLock(s,z,_);
{
  acquire(z);
  t := [x];
  [x] := w;
  [x + 1] := w;
  release(z);
}
