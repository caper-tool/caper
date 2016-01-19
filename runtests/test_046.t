// NAME: Assertion test 1
// RESULT: ACCEPT

function foo(x)
  requires x |-> 0;
  ensures true;
{
  assert x |-> 0;
  [x] := 1;
  assert x |-> 1;
}

