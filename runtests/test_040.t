// NAME: Region creation 1
// RESULT: ACCEPT

/* DESCRIPTION: Create a simple region.
*/

region Ra(r,x) {
  guards 0;
  interpretation {
    0 : x |-> 0;
  }
  actions {
  }
}

function foo(x)
  requires x |-> 0;
  ensures Ra(r,x,0);
{
}

