namespace CsNullable;

public class Nullable
{
    public static string? CsString()
    {
        var x = new Random().Next(2);
        return x == 0 ? "a string" : null;
    }
}