// NAME: Zero-guard test 3
// RESULT: ACCEPT

region Counter(r, x) {
  guards 0;
  interpretation {
    0 : x |-> 0;
    1 : x |-> 1;
  }
  actions {
    : 0 ~> 1;
  }
}

function makeCounter()
  requires true;
  ensures Counter(r, ret, v) &*& v <= 1;
{
    v := alloc(1);
    [v] := 0;
    return v;
}
