// NAME: Parse parameterised guard 3
// RESULT: ERROR

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
  ensures Ra(r, x, 0) &*& r@(G{0 | n > 0});
{
}
