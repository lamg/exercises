namespace Problems;

public partial class Problems
{
    public static long VeryBigSum(List<long> ar)
    {
        return ar.Aggregate((acc, x) => acc + x);
    }
}
