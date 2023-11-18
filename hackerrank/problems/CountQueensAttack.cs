namespace Problems;
using System.Collections.Generic;

public partial class Problems
{

    public static int CountQueensAttack(int n, int r_q, int c_q, List<List<int>> obstacles)
    {
        // the idea here is calculating the distance between the queen and the closest obstacle in each direction
        // if there's no obstacle then the distance to the edge of the board is used   
        int up = n - r_q;
        int down = r_q - 1;
        int left = c_q - 1;
        int right = n - c_q;
        int upLeft = Math.Min(up, left);
        int upRight = Math.Min(up, right);
        int downLeft = Math.Min(down, left);
        int downRight = Math.Min(down, right);

        foreach (var obstacle in obstacles)
        {
            if (obstacle[0] > r_q && obstacle[1] == c_q)
            {
                up = Math.Min(up, obstacle[0] - r_q - 1);
            }
            else if (obstacle[0] < r_q && obstacle[1] == c_q)
            {
                down = Math.Min(down, r_q - obstacle[0] - 1);
            }
            else if (obstacle[1] < c_q && obstacle[0] == r_q)
            {
                left = Math.Min(left, c_q - obstacle[1] - 1);
            }
            else if (obstacle[1] > c_q && obstacle[0] == r_q)
            {
                right = Math.Min(right, obstacle[1] - c_q - 1);
            }
            else if (obstacle[0] > r_q && obstacle[1] < c_q && obstacle[0] - r_q == c_q - obstacle[1])
            {
                upLeft = Math.Min(upLeft, obstacle[0] - r_q - 1);
            }
            else if (obstacle[0] > r_q && obstacle[1] > c_q && obstacle[0] - r_q == obstacle[1] - c_q)
            {
                upRight = Math.Min(upRight, obstacle[0] - r_q - 1);
            }
            else if (obstacle[0] < r_q && obstacle[1] < c_q && r_q - obstacle[0] == c_q - obstacle[1])
            {
                downLeft = Math.Min(downLeft, r_q - obstacle[0] - 1);
            }
            else if (obstacle[0] < r_q && obstacle[1] > c_q && r_q - obstacle[0] == obstacle[1] - c_q)
            {
                downRight = Math.Min(downRight, r_q - obstacle[0] - 1);
            }
        }

        return up + down + left + right + upLeft + upRight + downLeft + downRight;
    }
}