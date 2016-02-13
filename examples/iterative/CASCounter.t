// Compare-and-swap Counter

region Counter(r, x) {
  guards %INCREMENT;
  interpretation {
    n : x |-> n;
  }
  actions {
    n < m | INCREMENT[_] : n ~> m;
  }
}

function makeCounter()
  requires true;
  ensures Counter(r, ret, 0) &*& r@(INCREMENT[1p]);
{
    v := alloc(1);
    [v] := 0;
    return v;
}

function incr(x)
  requires Counter(r, x, v0) &*& r@(INCREMENT[p]);
  ensures Counter(r, x, v1) &*& v1 > v0 &*& r@(INCREMENT[p]);
{
    do 
      invariant Counter(r, x, vi) &*& r@(INCREMENT[p]) &*& (b = 1 ? vi > v0 : vi >= v0);
    {
        v := [x];
        b := CAS(x, v, v + 1);
    } while (b = 0);
    return v;
}

function read(x)
  requires Counter(r, x, v0);
  ensures Counter(r, x, v1) &*& ret >= v0 &*& ret <= v1;
{
    v := [x];
    return v;
}
