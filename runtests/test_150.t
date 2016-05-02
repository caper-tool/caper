// NAME: Predicate test 1
// RESULT: ACCEPT
predicate foo();

function bar()
	requires foo();
	ensures foo();
{
}
