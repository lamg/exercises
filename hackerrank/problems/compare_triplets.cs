namespace Problems;

public partial class Problems
{
    public static List<int> CompareTriplets(List<int> a, List<int> b)
    {
        var r = a.Zip(b).Aggregate(new List<int> { 0, 0 }, (acc, x) =>
        {
            if (x.First > x.Second)
            {
                acc[0]++;
            }
            else if (x.First < x.Second)
            {
                acc[1]++;
            }
            return acc;
        });

        return r;
    }
}