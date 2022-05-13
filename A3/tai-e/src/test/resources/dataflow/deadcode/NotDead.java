class NotDead {
    int a;

    void foo(int x, int y) {
        int a;
        if (x > y) {
            a = 0;
        } else {
            a = 1;
        }
        use(a);
    }

    int bar() {
        int x = 1;
        int y = x;
        int z = y;
        return z;
    }

    void use(int n) {
    }

    int unreachableSwitchBranch(NotDead C) {
        int x = 2, y, z;
        switch (x) {
            case 1: y = 100; break; // unreachable branch
            case 2: z = C.a;
                y = 200;
            case 3: y = C.a; break; // fall through
            default: y = 666; // unreachable branch
        }
        return y;
    }
}