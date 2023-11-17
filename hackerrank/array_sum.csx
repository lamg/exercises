using System;

static int simpleArraySum(List<int> xs)
{
    return xs.Aggregate(0, (acc, x) => acc + x);
}

Console.WriteLine(simpleArraySum(new List<int> { 1, 2, 3, 4, 10, 11 }));