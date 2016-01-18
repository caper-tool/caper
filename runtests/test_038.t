// NAME: Region in region 2
// RESULT: ACCEPT

/* DESCRIPTION: We can put a region into a region in a way that is self-consistent
*/

region Ra(r,x) {
  guards FOO;
  interpretation {
    0 : x |-> 0;
    1 : x |-> 1 &*& Ra(r,x,1) &*& r@(FOO);
  }
  actions {
    FOO : 0 ~> 1;
  }
}

function foo(x)
  requires Ra(r,x,0) &*& r@(FOO);
  ensures Ra(r,x,1);
{
  [x] := 1;
}

