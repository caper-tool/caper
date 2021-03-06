// NAME: Guard equivalence test 1
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
  ensures Ra(r, x, n) &*& r@(SET[a] * SET[b]);
{
}
