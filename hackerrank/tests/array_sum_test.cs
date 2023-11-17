namespace tests;

using Problems;

public class ProblemsTest
{
    [Fact]
    public void SimpleArraySumTest()
    {
        var r = Problems.SimpleArraySum([1, 2, 3]);
        Assert.Equal(6, r);
    }

    [Fact]
    public void CompareTripletsTest()
    {
        var r = Problems.CompareTriplets([1, 2, 3], [3, 2, 1]);
        Assert.Equal([1, 1], r);
    }
}