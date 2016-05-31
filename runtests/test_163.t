// NAME: Cell conditions 2
// RESULT: ACCEPT

function test(a, b)
	requires a |-> _ &*& b |-> #cells(2);
	ensures ret != 0;
{
        return (a - b);
}
