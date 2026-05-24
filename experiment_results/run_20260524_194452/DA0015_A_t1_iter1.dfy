// <vc-preamble>
predicate ValidInput(input: string) {
    |input| > 0
}

predicate ValidOutput(result: string) {
    result == "Kuro" || result == "Shiro" || result == "Katie" || result == "Draw" || result == ""
}

function OptimalScore(ribbon: string, turns: int): int
    requires |ribbon| >= 0 && turns >= 0
    ensures OptimalScore(ribbon, turns) >= 0
{
    var maxFreq := MaxCharFreq(ribbon);
    var length := |ribbon|;
    if turns == 1 && maxFreq == length then 
        if maxFreq > 0 then maxFreq - 1 else 0
    else if length < maxFreq + turns then length
    else maxFreq + turns
}
// </vc-preamble>

// <vc-helpers>
function MaxCharFreq(s: string): int
    ensures MaxCharFreq(s) >= 0
    ensures MaxCharFreq(s) <= |s|
{
    MaxCharFreqHelper(s, 0, 0)
}

function MaxCharFreqHelper(s: string, idx: int, maxSoFar: int): int
    requires 0 <= idx <= 256
    requires maxSoFar >= 0
    ensures MaxCharFreqHelper(s, idx, maxSoFar) >= 0
    ensures MaxCharFreqHelper(s, idx, maxSoFar) <= |s|
    decreases 256 - idx
{
    if idx >= 256 then maxSoFar
    else
        var freq := CountChar(s, idx as char);
        var newMax := if freq > maxSoFar then freq else maxSoFar;
        MaxCharFreqHelper(s, idx + 1, newMax)
}

function CountChar(s: string, c: char): int
    ensures CountChar(s, c) >= 0
    ensures CountChar(s, c) <= |s|
{
    CountCharHelper(s, c, 0, 0)
}

function CountCharHelper(s: string, c: char, i: int, count: int): int
    requires 0 <= i <= |s|
    requires 0 <= count <= i
    ensures CountCharHelper(s, c, i, count) >= 0
    ensures CountCharHelper(s, c, i, count) <= |s|
    decreases |s| - i
{
    if i >= |s| then count
    else if s[i] == c then CountCharHelper(s, c, i + 1, count + 1)
    else CountCharHelper(s, c, i + 1, count)
}

function Max3(a: int, b: int, c: int): int
    ensures Max3(a, b, c) >= a
    ensures Max3(a, b, c) >= b
    ensures Max3(a, b, c) >= c
    ensures Max3(a, b, c) == a || Max3(a, b, c) == b || Max3(a, b, c) == c
{
    if a >= b && a >= c then a
    else if b >= c then b
    else c
}

function SplitLines(s: string): seq<string>
    ensures |SplitLines(s)| >= 0
{
    SplitLinesHelper(s, 0, 0, [])
}

function SplitLinesHelper(s: string, start: int, i: int, acc: seq<string>): seq<string>
    requires 0 <= start <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then
        if start <= |s| then acc + [s[start..|s|]]
        else acc
    else if s[i] == '\n' then
        SplitLinesHelper(s, i + 1, i + 1, acc + [s[start..i]])
    else
        SplitLinesHelper(s, start, i + 1, acc)
}

function ParseInt(s: string): int
    ensures ParseInt(s) >= 0
{
    ParseIntHelper(s, 0, 0)
}

function ParseIntHelper(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    requires acc >= 0
    ensures ParseIntHelper(s, i, acc) >= 0
    decreases |s| - i
{
    if i >= |s| then acc
    else if s[i] >= '0' && s[i] <= '9' then
        ParseIntHelper(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    else
        ParseIntHelper(s, i + 1, acc)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures var lines := SplitLines(input);
            if |lines| < 4 then result == ""
            else (
                var turns := ParseInt(lines[0]);
                var s0 := lines[1];
                var s1 := lines[2]; 
                var s2 := lines[3];
                var score0 := OptimalScore(s0, turns);
                var score1 := OptimalScore(s1, turns);
                var score2 := OptimalScore(s2, turns);
                var maxScore := Max3(score0, score1, score2);
                var winners := (if score0 == maxScore then 1 else 0) + (if score1 == maxScore then 1 else 0) + (if score2 == maxScore then 1 else 0);
                (winners > 1 ==> result == "Draw") &&
                (winners == 1 && score0 == maxScore ==> result == "Kuro") &&
                (winners == 1 && score1 == maxScore ==> result == "Shiro") &&
                (winners == 1 && score2 == maxScore ==> result == "Katie")
            )
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    if |lines| < 4 {
        result := "";
    } else {
        var turns := ParseInt(lines[0]);
        var s0 := lines[1];
        var s1 := lines[2];
        var s2 := lines[3];
        var score0 := OptimalScore(s0, turns);
        var score1 := OptimalScore(s1, turns);
        var score2 := OptimalScore(s2, turns);
        var maxScore := Max3(score0, score1, score2);
        var winners := (if score0 == maxScore then 1 else 0) + (if score1 == maxScore then 1 else 0) + (if score2 == maxScore then 1 else 0);
        if winners > 1 {
            result := "Draw";
        } else if score0 == maxScore {
            result := "Kuro";
        } else if score1 == maxScore {
            result := "Shiro";
        } else {
            result := "Katie";
        }
    }
}
// </vc-code>
