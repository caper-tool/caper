// NAME: Predicate test 3
// RESULT: REJECT
predicate foo();

function bar()
	requires foop();
	ensures true;
{
}
