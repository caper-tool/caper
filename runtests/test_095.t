// NAME: Parse parameterised guard 2
// RESULT: ACCEPT

region Ra(r, x) {
  guards #G;
  interpretation {
    0 : x |-> 0;
  }
  actions {
  }
}

function foo(x)
  requires x |-> 0;
  ensures Ra(r, x, 0) &*& r@(G{n | n > 0});
{
}
