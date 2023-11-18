namespace Problems;

public partial class Problems
{

    static int GetTopicCount(string a, string b)
    {
        var count = 0;
        for (var i = 0; i < a.Length; i++)
        {
            if (a[i] == '1' || b[i] == '1')
            {
                count++;
            }
        }
        return count;
    }

    public static List<int> acmTeam(List<string> topic)
    {
        var max = 0;
        var total = 0;
        for (var i = 0; i < topic.Count; i++)
        {
            for (var j = i + 1; j < topic.Count; j++)
            {
                var count = GetTopicCount(topic[i], topic[j]);
                if (count > max)
                {
                    max = count;
                    total = 1;
                }
                else if (count == max)
                {
                    total++;
                }
            }
        }
        return new List<int> { max, total };
    }
}
