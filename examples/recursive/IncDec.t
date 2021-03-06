// Increment Decrement

region IncDec(r, x) {
  guards INC * DEC;
  interpretation {
    n : x |-> n;
  }
  actions {
    n < m | INC : n ~> m;
    n > m | DEC : n ~> m;
    INC * DEC : n ~> m;
  }
}

function makeCounter()
  requires true;
  ensures IncDec(r, ret, 0) &*& r@(INC * DEC);
{
    v := alloc(1);
    [v] := 0;
    return v;
}

function increment(x, k)
  requires IncDec(r, x, v0) &*& r@INC &*& k > 0;
  ensures IncDec(r, x, v1) &*& r@INC &*& v1 <= v0 + k;
{
    v := [x];
    b := CAS(x, v, v + k);
    if (b = 0) {
        v := increment(x, k);
    }
    return v;
}

function decrement(x, k)
  requires IncDec(r, x, v0) &*& r@DEC &*& k > 0;
  ensures IncDec(r, x, v1) &*& r@DEC &*& v1 >= v0 - k;
{
    v := [x];
    b := CAS(x, v, v - k);
    if (b = 0) {
        v := decrement(x, k);
    }
    return v;
}

function read(x)
  requires IncDec(r, x, v0);
  ensures IncDec(r, x, v1);
{
    v := [x];
    return v;
}
