// NAME: Region creation 5
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
  requires x |-> 0;
  ensures r@(FOO) &*& Ra(r,x,0);
{
    [x] := 1;
}

