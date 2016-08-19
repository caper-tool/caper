// NAME: Compound GA decl with counting guards
// RESULT: ACCEPT

// DESCRIPTION: basic parsing of counting guard algebra declaration
region Foo(r) {
  guards %F * |G|;
  interpretation {
    0 : true;
  }
  actions {}
}