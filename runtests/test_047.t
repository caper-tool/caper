// NAME: Assertion test 2
// RESULT: REJECT

function foo(x)
  requires x |-> 0;
  ensures true;
{
  assert x |-> 0;
  [x] := 1;
  assert x |-> 0;
}

