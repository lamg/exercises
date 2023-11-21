namespace Problems;

public partial class Problems
{
    public static void MiniMaxSum(List<int> arr)
    {
        var xs = new List<long>();
        arr.ForEach(x => xs.Add(x));

        var sum = xs.Sum();
        var min = sum - xs.Max();
        var max = sum - xs.Min();
        Console.WriteLine($"{min} {max}");
    }
}