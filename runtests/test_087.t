// NAME: Guard equivalence test 2
// RESULT: ACCEPT

region Ra(r, x) {
  guards %SET;
  interpretation {
    n : x |-> n;
  }
  actions {
  }
}

function test(x)
  requires Ra(r, x, n) &*& r@(SET[a] * SET[b]);
  ensures Ra(r, x, n) &*& r@(SET[a]) &*& r@(SET[b]);
{
}
