
public class MyTest {
    public MyTest() {
    }

    int fun() {
        int a = 0;
        int b = 0;
        int c=51;
        if (a > 0) {
            int m = a + b;
            b = m + a;
        } else {
            int k = b;
            return k * 2 + a;
        }
        return a * b /c +25;
    }
}