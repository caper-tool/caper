// NAME: Region creation 11
// RESULT: REJECT

region Ra(r, x) {
  guards FOO;
  interpretation {
    0 : x |-> 0;
  }
  actions {
  }
}

region Rb(r, x) {
  guards BAR;
  interpretation {
    0 : Ra(r, x, 0);
  }
  actions {
  }
}

function foo(x)
  requires x |-> 0;
  ensures Ra(r, x, 0);
{
}

function bar(x)
  requires Ra(r, x, 0);
  ensures Ra(r, x, 0) &*& Rb(s, x, 0);
{
}