// NAME: Set guard test 2
// RESULT: REJECT

function foo()
  requires r@G{ x | n0 < x, x < n1 } &*& n0 < m &*& m <= n1;
  ensures r@G(m);
{
}
