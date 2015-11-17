// NAME: Misused Guards in Region Declaration 2
// RESULT: REJECT

region Foo(r) {
        guards BAR;
        interpretation {
                0 : true;
                1 : true;
        }
        actions {
                BAR[_] : 0 ~> 1;
        }
}
