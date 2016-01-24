// NAME: Parse variable assertion
// RESULT: ACCEPT

region Ra(r, x) {
  guards 0;
  interpretation {
    n : x |-> n;
  }
  actions {
  }
}

function test_variable_assertion(x)
  requires Ra(r, x, n) &*& s = r;
  ensures true;
{
}
