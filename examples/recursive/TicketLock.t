// Ticket Lock

region TLock(r, x) {
  guards #NEXT;
  interpretation {
    n : x |-> m &*& (x + 1) |-> n &*& r@NEXT{ k | k >= m } &*& m >= n;
  }
  actions {
    NEXT{ k | n <= k, k < m } : n ~> m;
  }
}

function makeLock()
  requires true;
  ensures TLock(r, ret, 0);
{
    v := alloc(2);
    [v + 0] := 0;
    [v + 0] := 0;
    return v;
}

function incr(x)
  requires TLock(r, x, _);
  ensures TLock(r, x, n) &*& r@TAKE(ret) &*& ret >= n;
{
    t := [x + 0];
    b := CAS(x + 0, t, t + 1);
    if (b = 0) {
        t := incr(x);
    }
    return t;
}

function wait(x, t)
    requires TLock(r, x, n) &*& r@TAKE(t) &*& t >= n;
    ensures TLock(r, x, t) &*& r@TAKE(t);
{
    v := [x + 1];
    if (v < t) {
        wait(x, t);
    }
}

function lock(x)
  requires TLock(r, x, _);
  ensures TLock(r, x, n) &*& r@TAKE(n);
{
    t := incr(x);
    wait(x, t);    
}

function unlock(x)
  requires TLock(r, x, n) &*& r@TAKE(n);
  ensures TLock(r, x, _);
{
    v := [x + 1];
    [x + 1] := v + 1;
}
