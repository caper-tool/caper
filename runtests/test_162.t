// NAME: Cell conditions 1
// RESULT: ACCEPT

function test(a, b)
	requires a |-> _ &*& b |-> _;
	ensures ret != 0;
{
        return (a - b);
}
