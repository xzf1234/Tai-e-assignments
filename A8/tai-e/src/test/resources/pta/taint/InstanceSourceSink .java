class InstanceSourceSink {
    private static String f;
    private static String[] a = new String[5];


    public static void main(String args[]) {
        InstanceSourceSink source = new InstanceSourceSink();
        a[1] = source.instanceSource();
        InstanceSourceSink sink = new InstanceSourceSink();
        sink.instanceSink(a[1]);
    }

    public String instanceSource() {
        return new String();
    }

    public void instanceSink(String s) {

    }

}