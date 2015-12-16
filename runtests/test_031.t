// NAME: Guarded transition test 2
// RESULT: REJECT

/* DESCRIPTION: Simple instance of guarded transitions
*/

region Ra(r,x) {
  guards FOO * BAR;
  interpretation {
    0 : x |-> 0;
    1 : x |-> 1;
    2 : x |-> 2;
  }
  actions {
    n2 > n1 | FOO : n1 ~> n2;
  }
}

function foo(x)
  requires Ra(r,x,_) &*& r@(FOO);
  ensures Ra(r,x,1) &*& r@(FOO);
{
  [x] := 1;
}
