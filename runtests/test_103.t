// NAME: Set guard test 3
// RESULT: ACCEPT

function foo()
  requires r@G{ x | n0 < x, x < n1 } &*& n0 < m &*& m < n1;
  ensures r@G(m) &*& r@G{x | n0 < x, x < m} &*& r@G{x | m < x, x < n1};
{
}
