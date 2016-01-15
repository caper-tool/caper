// NAME: Region in region 3/Guarantee
// RESULT: REJECT

/* DESCRIPTION: We can't use FOO to go from state 1 to 0, when FOO is in the region.
*/

region Ra(r,x) {
  guards FOO;
  interpretation {
    0 : x |-> 0;
    1 : x |-> 1 &*& Ra(r,x,1) &*& r@(FOO);
  }
  actions {
    FOO : 0 ~> 1;
    FOO : 1 ~> 0;
  }
}

function foo(x)
  requires Ra(r,x,0) &*& r@(FOO);
  ensures true;
{
  [x] := 1;
  [x] := 0;
}

