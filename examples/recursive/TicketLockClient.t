// Ticket Lock

region TLock(r, x) {
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
  ensures TLock(r, ret, _);
{
    v := alloc(2);
    [v + 0] := 0;
    [v + 1] := 0;
    return v;
}

function incr(x)
  requires TLock(r, x, _);
  ensures TLock(r, x, n) &*& r@NEXT(ret) &*& ret >= n;
{
    t := [x + 0];
    b := CAS(x + 0, t, t + 1);
    if (b = 0) {
        t := incr(x);
    }
    return t;
}

function wait(x, t)
    requires TLock(r, x, n) &*& r@NEXT(t) &*& t >= n;
    ensures TLock(r, x, t) &*& r@NEXT(t);
{
    v := [x + 1];
    if (v < t) {
        wait(x, t);
    }
}

function acquire(x)
  requires TLock(r, x, _);
  ensures TLock(r, x, n) &*& r@NEXT(n);
{
    t := incr(x);
    wait(x, t);    
}

function release(x)
  requires TLock(r, x, n) &*& r@NEXT(n);
  ensures TLock(r, x, _);
{
    v := [x + 1];
    [x + 1] := v + 1;
}

region Client(r, x, s, z) {
  guards 0;
  interpretation {
    0 : TLock(s, z, k) &*& (x |-> a &*& (x+1) |-> a \/ s@NEXT(k));
  }
  actions {
  }
}

function foo(x, z, w)
  requires Client(r, x, s, z,0) &*& TLock(s,z,_);
  ensures Client(r,x,s,z,0) &*& TLock(s,z,_);
{
  acquire(z);
  t := [x];
  [x] := w;
  [x + 1] := w;
  release(z);
}
