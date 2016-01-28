// Blocking Counter

region Counter(r,x) {
  guards %INCREMENT * OWN;
  interpretation {
    n >= 0 | n : k = 0 ? x |-> n &*& r@(OWN) : x |-> -1;
  }
  actions {
    n >= 0, n < m | INCREMENT[_] * OWN : n ~> m;
  }
}

function makeCounter()
  requires true;
  ensures Counter(r,ret,0) &*& r@(INCREMENT[1p]);
{
    v := alloc(1);
    [v] := 0;
    return v;
}

function incr(x)
  requires Counter(r,x,v0) &*& r@(INCREMENT[p]);
  ensures Counter(r,x,v1) &*& v1 > v0 &*& r@(INCREMENT[p]);
{
  v := [x];
  if (v = -1) {
    v := incr_rec(x);
  } else {
    b := CAS(x, v, -1);
    if (b = 0) {
      v := incr_rec(x);
    } else {
      [x] := v + 1;
    }
  }
  return v;
}

function read(x)
  requires Counter(r,x,v0);
  ensures Counter(r,x,v1) &*& ret >= v0 &*& ret <= v1;
{
  v := [x];
  if (v = -1) {
    v := read_rec(x);
  }
  return v;
}
