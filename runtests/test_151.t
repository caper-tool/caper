// NAME: Predicate test 2
// RESULT: REJECT
predicate foo();

function bar()
	requires true;
	ensures foo();
{
}
