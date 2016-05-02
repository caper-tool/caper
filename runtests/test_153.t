// NAME: Predicate test 4
// RESULT: REJECT
predicate foo();

function bar()
	requires foo();
	ensures foo() &*& foo();
{
}
