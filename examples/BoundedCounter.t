// Bounded counter

region BCounter(r,x) {
  guards %INCREMENT;
  interpretation {
    0 : x |-> 0;
    1 : x |-> 1;
    2 : x |-> 2;
  }
  actions {
    n < 2 | INCREMENT[_] : n ~> n + 1;
    INCREMENT[_] : 2 ~> 0;
  }
}

function makeCounter()
  requires true;
  ensures BCounter(r,ret,0) &*& r@(INCREMENT[1p]); {
    v := alloc(1);
    [v] := 0;
    return v;
}

function incr(x)
  requires BCounter(r,x,v0) &*& r@(INCREMENT[p]);
  ensures BCounter(r,x,v1) &*& r@(INCREMENT[p]) &*& (p = 1p ? ret = v0 &*& (v0 < 2 ? v1 = (v0 + 1) : v1 = 0) : true); {
    do {
        v := [x];
        b := CAS(x, v, v + 1);
    } while (b = 0);
    return v;
}

function read(x)
  requires BCounter(r,x,v0) &*& r@(INCREMENT[p]);
  ensures BCounter(r,x,v1) &*& r@(INCREMENT[p]) &*& (p != 1p ? ret = v0 : true) &*& (p != 1p ? v0 = v1 : true); {
    v := [x];
    return v;
}
