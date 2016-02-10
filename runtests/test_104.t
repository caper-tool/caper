// NAME: Set guard test 4
// RESULT: ACCEPT

function foo()
  requires r@G(m) &*& r@G{x | n0 < x, x < m} &*& r@G{x | m < x, x < n1};
  ensures r@G{ x | n0 < x, x < n1 };
{
}
