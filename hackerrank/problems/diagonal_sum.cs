namespace Problems;

public partial class Problems
{
    public static int DiagonalDifference(List<List<int>> arr)
    {
        var n = arr.Count;
        var d1 = 0;
        var d2 = 0;
        for (var i = 0; i < n; i++)
        {
            d1 += arr[i][i];
            d2 += arr[i][n - i - 1];
        }
        return Math.Abs(d1 - d2);
    }
}
