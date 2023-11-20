namespace Problems;

public partial class Problems
{
    public static long TaumBirthday(long b, long w, long bc, long wc, long z)
    {
        var costBlack = Math.Min(bc, wc + z);
        var costWhite = Math.Min(wc, bc + z);
        var totalCost = b * costBlack + w * costWhite;
        return totalCost;
    }
}