// NAME: Set guard test 1
// RESULT: ACCEPT

function foo(x)
  requires r@G{ x | n0 < x, x < n1 } &*& n0 < m &*& m < n1;
  ensures r@G(m);
{
}
