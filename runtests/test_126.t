// NAME: Region types don't match
// RESULT: REJECT

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
  requires Rb(r,x,0);
  ensures Ra(r,x,0);
{
}
