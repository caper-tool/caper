// NAME: Region creation 10
// RESULT: ACCEPT

region Ra(r, x) {
  guards FOO;
  interpretation {
    0 : x |-> 0;
  }
  actions {
  }
}

region Rb(s, x) {
  guards BAR;
  interpretation {
    0 : Ra(r, x, 0);
  }
  actions {
  }
}

function foo(x)
  requires x |-> 0;
  ensures Ra(r, x, 0) &*& Rb(s, x, 0);
{
}