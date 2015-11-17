// NAME: Misused Guards in Region Declaration 1
// RESULT: REJECT

region Foo(r) {
        guards BAR;
        interpretation {
                0 : true;
                1 : true;
        }
        actions {
                FOO : 0 ~> 1;
        }
}
