// NAME: Region creation 2
// RESULT: ACCEPT

/* DESCRIPTION: Region creation with a guard.
*/

region Ra(r,x) {
  guards FOO;
  interpretation {
    0 : x |-> 0;
  }
  actions {
  }
}

function foo(x)
  requires x |-> 0;
  ensures Ra(r,x,0) &*& r@(FOO);
{
}

