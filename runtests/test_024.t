// NAME: Correct Guards in Region Declaration 1
// RESULT: ACCEPT

region Foo(r) {
        guards BAR;
        interpretation {
                0 : true;
                1 : true;
        }
        actions {
                BAR : 0 ~> 1;
        }
}
