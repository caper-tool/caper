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
    do
      invariant Counter(r,x,vi) &*& r@(INCREMENT[p]) &*& vi >= v0 &*& (b = 0 ? true : r@(OWN) &*& v = vi)
    {
        v := [x];
        if (v = -1) {
            b := 0;
        } else {
            b := CAS(x, v, -1);
        }
    } while (b = 0);
    [x] := v + 1;
    return v;
}

function read(x)
  requires Counter(r,x,v0);
  ensures Counter(r,x,v1) &*& ret >= v0 &*& ret <= v1;
{
    do
      invariant Counter(r,x,vi) &*& vi >= v0 &*& (v >= 0 ? v0 <= v &*& v <= vi : v = -1)
    {
        v := [x];
    } while (v = -1);
    return v;
}
