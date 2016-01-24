// NAME: Parse permission assertion 5
// RESULT: ACCEPT

region Ra(r, x) {
  guards %SET;
  interpretation {
    n : x |-> n;
  }
  actions {
  }
}

function test_permission_assertion(x)
  requires Ra(r, x, n) &*& r@(SET[1p]);
  ensures true;
{
}
