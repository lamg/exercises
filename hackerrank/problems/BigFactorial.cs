namespace Problems;
using System.Text;
public partial class Problems
{
    public static void ExtraLongFactorials(int n)
    {
        Console.WriteLine(Factorial(n));
    }

    public static string Factorial(int n)
    {
        int[] res = new int[500];
        res[0] = 1;
        int res_size = 1;

        for (int x = 2; x <= n; x++)
        {
            res_size = Multiply(x, res, res_size);
        }

        StringBuilder result = new();
        for (int i = res_size - 1; i >= 0; i--)
        {
            result.Append(res[i]);
        }

        return result.ToString();
    }

    static int Multiply(int x, int[] res, int res_size)
    {
        int carry = 0;
        for (int i = 0; i < res_size; i++)
        {
            int prod = res[i] * x + carry;
            res[i] = prod % 10;
            carry = prod / 10;
        }

        while (carry != 0)
        {
            res[res_size] = carry % 10;
            carry = carry / 10;
            res_size++;
        }
        return res_size;
    }
}
