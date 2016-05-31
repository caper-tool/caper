// NAME: Cell conditions 3
// RESULT: ACCEPT

function test(a, b)
	requires a |-> #cells(2) &*& b |-> _;
	ensures ret != 0;
{
        return (a - b);
}
