// NAME: Disjunction test 1
// RESULT: ACCEPT

function foo()
  requires true;
  ensures true \/ false;
{
}
