namespace Problems;

public partial class Problems
{

    public static List<Tuple<int, int>> Combinations(List<int> set)
    {
        var combinations = new List<Tuple<int, int>>();
        for (int i = 0; i < set.Count; i++)
        {
            for (int j = i + 1; j < set.Count; j++)
            {
                combinations.Add(Tuple.Create(set[i], set[j]));
            }
        }
        return combinations;
    }

    public static List<List<T>> Permutations<T>(List<T> xs)
    {
        if (xs.Count == 1)
        {
            return new List<List<T>> { xs };
        }
        var permutations = new List<List<T>>();
        for (var i = 0; i < xs.Count; i++)
        {
            var ys = new List<T>(xs);
            ys.RemoveAt(i);
            var zs = Permutations(ys);
            zs.ForEach(z =>
            {
                z.Insert(0, xs[i]);
                permutations.Add(z);
            });
        }
        return permutations;
    }

    public static bool IsMagicSquare(List<List<int>> xss)
    {
        var n = xss.Count;
        var sum = 0;
        for (var i = 0; i < n; i++)
        {
            sum += xss[i][i];
        }
        var sum2 = 0;
        for (var i = 0; i < n; i++)
        {
            sum2 += xss[i][n - i - 1];
        }
        if (sum != sum2)
        {
            return false;
        }
        for (var i = 0; i < n; i++)
        {
            var sum3 = 0;
            for (var j = 0; j < n; j++)
            {
                sum3 += xss[i][j];
            }
            if (sum3 != sum)
            {
                return false;
            }
        }
        for (var i = 0; i < n; i++)
        {
            var sum3 = 0;
            for (var j = 0; j < n; j++)
            {
                sum3 += xss[j][i];
            }
            if (sum3 != sum)
            {
                return false;
            }
        }
        return true;
    }

    public static List<List<int>> CreateSquare(List<int> xs)
    {
        List<List<int>> square = new List<List<int>>{new() {0, 0, 0}, new() {0, 5, 0}, new() {0, 0, 0}};
        var n = 0;
        for (var i = 0; i < square.Count; i++)
        {
            for (var j = 0; j < square.Count; j++)
            {
                if (i != 1 || j != 1)
                {
                    square[i][j] = xs[n];
                    n++;
                }
            }

        }

        return square;
    }

    public static int TransformationCost(List<List<int>> xs, List<List<int>> ys)
    {
        var cost = 0;
        for (var i = 0; i < xs.Count; i++)
        {
            for (var j = 0; j < xs.Count; j++)
            {
                cost += Math.Abs(xs[i][j] - ys[i][j]);
            }
        }
        return cost;
    }

    public static int MagicSquare(List<List<int>> xss)
    {
        var permutations = Permutations(new List<int>{1, 2, 3, 4, 6, 7, 8, 9});
        var squares = permutations.Select(CreateSquare).Where(IsMagicSquare).ToList();
        var minCost = squares.Select(square => TransformationCost(xss, square)).ToList().Min();
        return minCost;
    }
}
