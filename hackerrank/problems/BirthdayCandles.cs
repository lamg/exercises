namespace Problems;

public partial class Problems
{
    public static int BirthdayCakeCandles(List<int> candles)
    {
        var max = 0;
        var count = 0;
        foreach (var candle in candles)
            if (candle > max)
            {
                max = candle;
                count = 1;
            }
            else if (candle == max)
            {
                count++;
            }

        return count;
    }
}