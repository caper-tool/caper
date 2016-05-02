// NAME: Region in region 2
// RESULT: ACCEPT

region Foo(r,x) {
        guards OWN;
        interpretation {
                0 : x |-> 0 &*& Bar(s,x,0) &*& s@BOWN;
                1 : x |-> 1 &*& Bar(s,x,1);
        }
        actions {
                OWN : 0 ~> 1;
        }
}

region Bar(s,y) {
        guards BOWN;
        interpretation {
                0 : true;
                1 : true;
        }
        actions {
                BOWN : 0 ~> 1;
        }
}

function test(x)
	requires Foo(r,x,0) &*& r@OWN;
	ensures Foo(r,x,1);
{
        [x] := 1;
}
