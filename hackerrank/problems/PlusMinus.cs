namespace Problems;

public partial class Problems
{
    public static void PlusMinus(List<int> arr)
    {
        var n = arr.Count;
        var pos = 0;
        var neg = 0;
        var zero = 0;
        foreach (var item in arr)
        {
            if (item > 0)
            {
                pos++;
            }
            else if (item < 0)
            {
                neg++;
            }
            else
            {
                zero++;
            }
        }
        Console.WriteLine($"{(double)pos / n:F6}");
        Console.WriteLine($"{(double)neg / n:F6}");
        Console.WriteLine($"{(double)zero / n:F6}");
    }
}
