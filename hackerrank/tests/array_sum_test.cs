namespace tests;

using Problems;

public class ProblemsTest
{
    [Fact]
    public void SimpleArraySumTest()
    {
        var r = Problems.SimpleArraySum([1, 2, 3]);
        Assert.Equal(6, r);
    }

    [Fact]
    public void CompareTripletsTest()
    {
        var r = Problems.CompareTriplets([1, 2, 3], [3, 2, 1]);
        Assert.Equal([1, 1], r);
    }

    [Fact]
    public void CombinationsTest()
    {
        var r = Problems.Combinations([1, 2, 3]);
        Assert.Equal([
            Tuple.Create(1, 2),
            Tuple.Create(1, 3),
            Tuple.Create(2, 3)
        ], r);
    }

    [Fact]
    public void Permutations()
    {
        var r = Problems.Permutations([1, 2, 3]);
        Assert.Equal([
            [1, 2, 3],
            [1, 3, 2],
            [2, 1, 3],
            [2, 3, 1],
            [3, 1, 2],
            [3, 2, 1]
        ], r);
    }

    static void PrintSquare(List<List<int>> square)
    {
        var n = square.Count;
        for (var i = 0; i < n; i++)
        {
            foreach (var x in square[i])
            {
                Console.Write(x + " ");
            }
            Console.WriteLine();
        }
    }
    [Fact]
    public void ShowMagicSquares()
    {
        var permutations = Problems.Permutations([1, 2, 3, 4, 6, 7, 8, 9]);
        var squares = permutations.Select(Problems.CreateSquare);
        var magic = squares.Where(Problems.IsMagicSquare).ToList();
        Assert.Equal(8, magic.Count);
        // foreach (var square in magic)
        // {
        //     PrintSquare(square);
        //     Console.WriteLine();
        // }
    }

    [Fact]
    public void CountQueensAttackTest()
    {
        List<List<int>> obstacles = [];
        var r = Problems.CountQueensAttack(4, 4, 4, obstacles);
        Assert.Equal(9, r);
    }
}