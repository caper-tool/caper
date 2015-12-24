// NAME: Unbounded region test 2
// RESULT: ACCEPT

/* DESCRIPTION: Simple instance of unbounded regions
*/

region Ra(r,x) {
  guards FOO;
  interpretation {
    n >= 0 | n : x |-> n;
  }
  actions {
    n2 > n1 | FOO : n1 ~> n2;
  }
}

function foo(x)
  requires Ra(r,x,n) &*& r@(FOO);
  ensures Ra(r,x,n+1) &*& r@(FOO);
{
  y := [x];
  [x] := y + 1;
}
