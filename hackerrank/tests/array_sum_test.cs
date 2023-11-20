namespace tests;

using Problems;
using Xunit.Abstractions;

public class ProblemsTest
{

    private readonly ITestOutputHelper _output;

    public ProblemsTest(ITestOutputHelper output)
    {
        _output = output;
    }

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
    struct TestCase
    {
        public long b;
        public long w;
        public long bc;
        public long wc;
        public long z;
        public long expected;
    }

    [Fact]
    public void TaumBirthdayTest()
    {
        var test0 = new List<TestCase>
        {
            new () { b = 81121308, w = 2772464, bc = 720682, wc = 615826, z = 14843 },
            new () { b = 6550863, w = 99744789, bc = 678609, wc = 64920, z = 289297 },
            new () { b = 32797220, w = 23367318, bc = 902640, wc = 429570, z = 404819 },
            new () { b = 36392904, w = 80519738, bc = 872118, wc = 344893, z = 400189 },
            new () { b = 49666210, w = 86374039, bc = 59438, wc = 359841, z = 438491 },
            new () { b = 59255837, w = 92618771, bc = 24658, wc = 947186, z = 683792 },
            new () { b = 42009279, w = 38068493, bc = 456255, wc = 246313, z = 200670 },
            new () { b = 58987449, w = 22313527, bc = 461810, wc = 182410, z = 378447 },
            new () { b = 32267458, w = 63495981, bc = 745764, wc = 170098, z = 441902 },
            new () { b = 83666934, w = 10563001, bc = 961640, wc = 539051, z = 424245 }
        };

        var test1 = new List<TestCase>
        {
            new() { b = 27984, w = 1402, bc = 619246, wc = 615589, z = 247954 },
            new () { b = 95677, w = 39394, bc = 86983, wc = 311224, z = 588538 },
            new () { b = 68406, w = 12718, bc = 532909, wc = 315341, z = 201009 },
            new () { b = 15242, w = 95521, bc = 712721, wc = 628729, z = 396706 },
            new () { b = 21988, w = 67781, bc = 645748, wc = 353796, z = 333199 },
            new () { b = 22952, w = 80129, bc = 502975, wc = 175136, z = 340236 },
            new () { b = 38577, w = 3120, bc = 541637, wc = 657823, z = 735060 },
            new () { b = 5943, w = 69851, bc = 674453, wc = 392925, z = 381074 },
            new () { b = 62990, w = 61330, bc = 310144, wc = 312251, z = 93023 },
            new () { b = 11152, w = 43844, bc = 788543, wc = 223872, z = 972572 }
        };

        var cases = new List<List<TestCase>> {test0, test1};
        var results = cases.SelectMany(ts =>
            ts.Select(t => Problems.TaumBirthday(t.b, t.w, t.bc, t.wc, t.z)));
        foreach (var r in results)
        {
            _output.WriteLine("result {0}",r);
        }
    }
}