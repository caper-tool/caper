// NAME: Disjunction test 4
// RESULT: REJECT

function foo(x)
  requires x = 0 \/ x = 1;
  ensures x = 0;
{
}
