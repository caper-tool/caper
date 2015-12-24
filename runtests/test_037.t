// NAME: Unbounded region test 4
// RESULT: ACCEPT

/* DESCRIPTION: Simple instance of unbounded regions
*/

region Ra(r,x) {
  guards %FOO;
  interpretation {
    n >= 0 | n : x |-> n;
  }
  actions {
    n2 > n1 | FOO[_] : n1 ~> n2;
  }
}

function foo(x)
  requires Ra(r,x,n) &*& r@(FOO[p]);
  ensures Ra(r,x,m) &*& r@(FOO[p]) &*& m > n;
{
  y := [x];
  CAS(x,y,y+1);
}
