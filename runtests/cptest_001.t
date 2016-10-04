// NAME: Guard Algebra Parsing |G|
// RESULT: ACCEPT

// DESCRIPTION: basic parsing of counting guard algebra declaration
region Foo(r) {
  guards |G|;
  interpretation {
    0 : true;
  }
  actions {}
}