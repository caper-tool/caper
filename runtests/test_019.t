// NAME: Loop test 2
// RESULT: ACCEPT

/* DESCRIPTION:
*/

function foo(x)
  requires true;
  ensures x <= 0;
{
  while (x > 0)
  invariant true
  {
    y := x;
  }
}
