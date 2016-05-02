// NAME: Predicate test 5
// RESULT: REJECT
predicate foo();

function bar()
	requires foo() &*& foo();
	ensures false;
{
}
