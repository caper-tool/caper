// NAME: Parse parameterised guard 6
// RESULT: REJECT

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
  ensures Ra(r, x, 0) &*& r@G();
{
}
