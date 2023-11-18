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
        // the idea here is to find all the combinations of team members
        // for each combination, calculate the number of topics they know
        // keep track of the maximum number of topics and the number of teams that know that many topics
        var maxTopics = 0; // maximum number of topics known by a team
        var teams = 0; // number of teams that know the maximum number of topics
        for (var i = 0; i < topic.Count; i++)
        {
            for (var j = i + 1; j < topic.Count; j++)
            {
                var count = GetTopicCount(topic[i], topic[j]);
                if (count > maxTopics)
                {
                    maxTopics = count;
                    teams = 1;
                }
                else if (count == maxTopics)
                {
                    teams++;
                }
            }
        }
        return new List<int> { maxTopics, teams };
    }
}
