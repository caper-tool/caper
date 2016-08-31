// NAME: Complex stability test
// RESULT: ACCEPT

/* DESCRIPTION: The interpretation of Bar should be stable since
        a thread can only set a Foo region's state to below n if
        it has (at least) the FOO guards from n-2 and up.
*/

region Foo(a,x) {
    guards #FOO;
    interpretation {
        n : x |-> n;
    }
    actions {
       m < n | FOO{x|m<=x} : k ~> n;
    }
}

region Bar(b,a,x) {
    guards 0;
    interpretation {
        n : Foo(a,x,m) &*& a@FOO(n) &*& m >= n;
    }
    actions {}
}
