// NAME: Allocation conditions
// RESULT: ACCEPT

function test()
	requires true;
	ensures ret != 0;
{
        a := alloc(1);
        b := alloc(1);
        return (a - b);
}
