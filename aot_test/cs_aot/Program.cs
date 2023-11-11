static UInt64 factorial(UInt64 n)
{
    // create a local function for calculating factorial
    static UInt64 fact(UInt64 n, UInt64 acc)
    {
        if (n == 0)
            return acc;
        else
            return fact(n - 1, n * acc);
    }
    return fact(n, 1);
}


Console.WriteLine("factorial(10) = {0}", factorial(10));
