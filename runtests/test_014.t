// NAME: Region in region
// RESULT: REJECT

/* DESCRIPTION: We shouldn't be able to put a region into itself in a way that is inconsistent with its own state!
*/

region Ra(r,x) {
  guards FOO;
  interpretation {
    0 : x |-> 0;
    1 : x |-> 1 &*& Ra(r,x,0) &*& r@(FOO);
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

function bar(x)
  requires Ra(r,x,1);
  ensures false;
{
  z := [x];
}
