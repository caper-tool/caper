// NAME: Region creation in atomic 1
// RESULT: ACCEPT

region Foo(r,x) {
        guards OWN;
        interpretation {
                0 : x |-> 0;
                1 : x |-> y &*& Bar(s,y,0);
        }
        actions {
                OWN : 0 ~> 1;
        }
}

region Bar(s,y) {
        guards 0;
        interpretation {
                0 : y |-> _;
        }
        actions {}
}

function test(x,y)
	requires Foo(r,x,0) &*& r@OWN &*& y |-> _;
	ensures Foo(r,x,1) &*& r@OWN;
{
        [x] := y;
}
