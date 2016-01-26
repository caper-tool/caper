// NAME: Region creation 4
// RESULT: REJECT

region Ra(r,x) {
  guards FOO;
  interpretation {
    0 : x |-> 0;
  }
  actions {
  }
}

function foo(x)
  requires x |-> 1;
  ensures r@(FOO) &*& Ra(r,x,0);
{
}

