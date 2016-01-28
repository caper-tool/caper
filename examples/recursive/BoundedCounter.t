// Bounded Counter

region BCounter(r, x) {
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
  ensures BCounter(r,  ret,0) &*& r@(INCREMENT[1p]); {
    v := alloc(1);
    [v] := 0;
    return v;
}
/*
function incr(x)
  requires BCounter(r, x, v0) &*& r@(INCREMENT[p]);
  ensures BCounter(r, x, v1) &*& r@(INCREMENT[p]) &*& (p = 1p ? ret = v0 &*& (v0 < 2 ? v1 = (v0 + 1) : v1 = 0) : true); {
    v := [x];
    if (v < 2) {
        w := v + 1;
    } else {
        w := 0;
    }
    b := CAS(x, v, w);
    if (b = 0) {
        v := incr(x);
    }
    return v;
}
*/
function read(x)
  requires BCounter(r, x, v0) &*& r@(INCREMENT[p]);
  ensures BCounter(r, x, v1) &*& r@(INCREMENT[p]) &*& (p = 1p ? ret = v0 &*& v0 = v1 : true); {
    v := [x];
    return v;
}
