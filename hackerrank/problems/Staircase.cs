namespace Problems;

public partial class Problems
{
    public static void Staircase(int n)
    {
        for (var i = 1; i <= n; i++)
        {
            Console.WriteLine(new string(' ', n - i) + new string('#', i));
        }
    }
}
