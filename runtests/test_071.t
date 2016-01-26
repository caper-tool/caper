// NAME: Fork test 4
// RESULT: REJECT

function forked(x)
  requires x |-> 0;
  ensures true;
{
  [x] := 1;
}

function forker()
  requires true;
  ensures true;
{
  x := alloc(1);
  fork forked(x);
}
