// NAME: Region creation 7
// RESULT: ACCEPT

region Ra(r, x) {
  guards FOO;
  interpretation {
    0 : x |-> 0;
  }
  actions {
  }
}

function foo(x)
  requires x |-> 0;
  ensures Ra(r, x, 0) &*& Ra(s, x, 0);
{
}
