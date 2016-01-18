// NAME: Region creation 3
// RESULT: ACCEPT

/* DESCRIPTION: Morally this should be accepted, however at present
 * Caper fails when it tries to consume guards for the region r that
 * doesn't yet exist.
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
  ensures r@(FOO) &*& Ra(r,x,0);
{
}

