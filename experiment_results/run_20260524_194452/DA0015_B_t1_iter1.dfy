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

function MaxCharFreqHelper(s: string, charIdx: int, best: int): int
    requires 0 <= charIdx <= 256
    requires best >= 0
    ensures MaxCharFreqHelper(s, charIdx, best) >= best
    ensures MaxCharFreqHelper(s, charIdx, best) <= |s|
    decreases 256 - charIdx
{
    if charIdx >= 256 then best
    else
        var freq := CountChar(s, charIdx as char);
        var newBest := if freq > best then freq else best;
        MaxCharFreqHelper(s, charIdx + 1, newBest)
}

function CountChar(s: string, c: char): int
    ensures CountChar(s, c) >= 0
    ensures CountChar(s, c) <= |s|
{
    CountCharHelper(s, c, 0)
}

function CountCharHelper(s: string, c: char, idx: int): int
    requires 0 <= idx <= |s|
    ensures CountCharHelper(s, c, idx) >= 0
    ensures CountCharHelper(s, c, idx) <= |s| - idx
    decreases |s| - idx
{
    if idx >= |s| then 0
    else
        var rest := CountCharHelper(s, c, idx + 1);
        if s[idx] == c then rest + 1 else rest
}

function Max3(a: int, b: int, c: int): int
    ensures Max3(a, b, c) >= a
    ensures Max3(a, b, c) >= b
    ensures Max3(a, b, c) >= c
    ensures Max3(a, b, c) == a || Max3(a, b, c) == b || Max3(a, b, c) == c
{
    if a >= b && a >= c then a
    else if b >= a && b >= c then b
    else c
}

function SplitLines(s: string): seq<string>
    ensures |SplitLines(s)| >= 0
{
    SplitLinesHelper(s, 0, 0)
}

function SplitLinesHelper(s: string, start: int, idx: int): seq<string>
    requires 0 <= start <= idx <= |s|
    decreases |s| - idx
{
    if idx >= |s| then
        if start <= |s| then [s[start..|s|]] else []
    else if s[idx] == '\n' then
        [s[start..idx]] + SplitLinesHelper(s, idx + 1, idx + 1)
    else
        SplitLinesHelper(s, start, idx + 1)
}

function ParseInt(s: string): int
{
    ParseIntHelper(s, 0, 0)
}

function ParseIntHelper(s: string, idx: int, acc: int): int
    requires 0 <= idx <= |s|
    decreases |s| - idx
{
    if idx >= |s| then acc
    else
        var c := s[idx];
        if '0' <= c <= '9' then
            ParseIntHelper(s, idx + 1, acc * 10 + (c as int - '0' as int))
        else
            acc
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
