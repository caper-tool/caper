// NAME: Assertion test 4
// RESULT: REJECT

function foo(x)
  requires x |-> z;
  ensures true;
{
  assert x |-> z;
  [x] := 1;
  assert x |-> z;
}

