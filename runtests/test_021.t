// NAME: Loop test 4
// RESULT: ACCEPT

/* DESCRIPTION:
*/

function foo(x)
  requires true;
  ensures ret <= 0;
{
  while (x > 0)
  invariant true
  {
    x := -1;
  }
  return x;
}
