// NAME: Region interpretation stability 1
// RESULT: ACCEPT

/* DESCRIPTION:
*/

region Ra(r,x) {
  guards FOO;
  interpretation {
    0 : x |-> 0;
    1 : x |-> 1;
    2 : x |-> 2;
  }
  actions {
    FOO : n ~> n + 1;
  }
}

region Rb(r,s,x) {
  guards BAR;
  interpretation {
    0 : Ra(s,x,z) &*& z >= 1;
    1 : Ra(s,x,_);
    2 : Ra(s,x,0) &*& s@(FOO);
  }
  actions {
  }
}
