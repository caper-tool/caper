// NAME: Zero-guard test 1
// RESULT: REJECT

region Counter(r, x) {
  guards 0;
  interpretation {
    n : x |-> n;
  }
  actions {
    n < m | : n ~> m;
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
