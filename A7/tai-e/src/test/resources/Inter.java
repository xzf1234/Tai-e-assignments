class Inter {
    public static void main(String[] args) {
        loopConst();
    }

    static void loopConst() {
        int[] a = new int[5];
        for (int i = 0; i < a.length; ++i) {
            a[i] = 666;
        }
        int x = a[3];
    }

}