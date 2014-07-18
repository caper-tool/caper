// Compare-and-swap counter

region Counter(r,x) {
  guards %INCREMENT;
  interpretation {
    n : x |-> n;
  }
  actions {
    INCREMENT[_] : n ~~> n + 1;
  }
}

function makeCounter()
  requires emp;
  ensures Counter(r,ret,0) * r@INCREMENT[1];
{
    v := alloc(1);
    [v] := 0;
    return v;
}

function incr(x)
  requires Counter(r,x,v0) * r@INCREMENT[p];
  ensures Counter(r,x,v1) * v1 > v0 * 
{
    do {
        v := [x];
        b := CAS(x, v, v + 1);
    } while (b = 0);
    return v;
}

function read(x) {
    v := [x];
    return v;
}
