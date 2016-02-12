// NAME: Set guard test 5
// RESULT: REJECT

function foo()
  requires r@G{x | n0 < x, x < m} &*& r@G{x | m < x, x < n1};
  ensures r@G{ x | n0 < x, x < n1 };
{
}
