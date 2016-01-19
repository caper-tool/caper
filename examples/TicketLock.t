// Ticket lock

region TLock(r,x) {
  guards #NEXT;
  interpretation {
    n : x |-> m &*& (x + 1) |-> n &*& r@(NEXT{ k | k >= m }) &*& m >= n;
  }
  actions {
    NEXT{ k | n <= k, k < m } : n ~> m;
  }
}

function makeLock()
  requires true;
  ensures TLock(r,ret,0); {
    v := alloc(2);
    [v + 0] := 0;
    [v + 0] := 0;
    return v;
}

function lock(x)
  requires TLock(r,x,_);
  ensures TLock(r,x,n) &*& r@(TAKE(n)); {
    do 
        invariant TLock(r,x,n) &*& (b = 1 ? r@(TAKE(t)) &*& t >= n : true)
    {
        t := [x + 0];
        b := CAS(x + 0, t, t + 1);
    } while (b = 0);
    do
        invariant TLock(r,x,n) &*& r@(TAKE(t)) &*& n <= t
    {
        v := [x + 1];
    } while(v < t);
}

function unlock(x)
  requires TLock(r,x,n) &*& r@(TAKE(n));
  ensures TLock(r,x,_); {
    v = [x + 1];
    [x + 1] := v + 1;
}
