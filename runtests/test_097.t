// NAME: Parse parameterised guard 4
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
  ensures Ra(r, x, 0) &*& r@G(1p);
{
}
