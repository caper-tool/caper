// NAME: Assertion test 3
// RESULT: ACCEPT

function foo(x)
  requires x |-> 0;
  ensures true;
{
  assert x |-> z;
  [x] := 1;
  assert x |-> z;
}

