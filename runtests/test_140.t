// NAME: Stability with parametrised transitions 5
// RESULT: ACCEPT

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
  ensures Counter(r, ret, 0);
{
    v := alloc(1);
    [v] := 0;
    return v;
}
