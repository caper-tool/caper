// Bounded counter

region BCounter(r,x) {
  guards %INCREMENT;
  interpretation {
    n : x |-> n;
  }
  actions {
    INCREMENT[_] : n < 2 | n ~~> n + 1;
    INCREMENT[_] : 2 ~~> 0;
  }
}

function makeCounter()
  requires emp;
  ensures BCounter(r,ret,0) * r@INCREMENT[1]; {
    v := alloc(1);
    [v] := 0;
    return v;
}

function incr(x)
  requires BCounter(r,x,v0) * r@INCREMENT[p];
  ensures BCounter(r,x,v1) * r@INCREMENT[p] * (p != 1 or ret = v0 and ((v0 < 2 and v1 = v0 + 1) or (v0 = 2 and v1 = 0)));  {
    do {
        v := [x];
        b := CAS(x, v, v + 1);
    } while (b = 0);
    return v;
}

function read(x)
  requires BCounter(r,x,v0) * r@INCREMENT[p];
  ensures BCounter(r,x,v1) * r@INCREMENT[p] * (p != 1 or ret = v0 and v0 = v1);  {
    v := [x];
    return v;
}
