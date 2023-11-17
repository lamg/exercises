namespace Problems;

public partial class Problems
{
    public static int SimpleArraySum(List<int> xs)
    {
        return xs.Aggregate(0, (acc, x) => acc + x);
    }
}

