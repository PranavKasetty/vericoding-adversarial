// <vc-preamble>
predicate ValidInputString(s: string)
{
    |s| >= 7 &&
    ContainsFourLines(s) &&
    AllLinesHaveFourValidIntegers(s)
}

predicate ContainsFourLines(s: string)
{
    CountNewlines(s, 0) >= 3
}

predicate AllLinesHaveFourValidIntegers(s: string)
{
    forall i :: 0 <= i < |s| ==> (s[i] == '0' || s[i] == '1' || s[i] == ' ' || s[i] == '\n')
}

predicate ParseInput(s: string, input_lines: seq<seq<int>>)
{
    |input_lines| == 4 &&
    (forall i :: 0 <= i < 4 ==> |input_lines[i]| == 4) &&
    (forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> 
        (input_lines[i][j] >= 0 && input_lines[i][j] <= 1)) &&
    StringContainsFourLinesOfFourIntegers(s, input_lines)
}

predicate StringContainsFourLinesOfFourIntegers(s: string, input_lines: seq<seq<int>>)
{
    |input_lines| == 4 &&
    (forall i :: 0 <= i < 4 ==> |input_lines[i]| == 4) &&
    ValidInputString(s)
}

predicate AccidentPossible(lanes: seq<seq<int>>)
    requires |lanes| == 4
    requires forall i :: 0 <= i < 4 ==> |lanes[i]| == 4
    requires forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> 
        (lanes[i][j] == 0 || lanes[i][j] == 1)
{
    exists i :: 0 <= i < 4 && AccidentAtLane(i, lanes)
}

predicate AccidentAtLane(i: int, lanes: seq<seq<int>>)
    requires 0 <= i < 4
    requires |lanes| == 4
    requires forall j :: 0 <= j < 4 ==> |lanes[j]| == 4
{
    (lanes[i][3] == 1 && (lanes[i][0] == 1 || lanes[i][1] == 1 || lanes[i][2] == 1)) ||
    (lanes[i][0] == 1 && lanes[(i + 3) % 4][3] == 1) ||
    (lanes[i][1] == 1 && lanes[(i + 2) % 4][3] == 1) ||
    (lanes[i][2] == 1 && lanes[(i + 1) % 4][3] == 1)
}
// </vc-preamble>

// <vc-helpers>
function CountNewlines(s: string, acc: int): int
{
    if |s| == 0 then acc
    else if s[0] == '\n' then CountNewlines(s[1..], acc + 1)
    else CountNewlines(s[1..], acc)
}

function ParseChar(c: char): int
    requires c == '0' || c == '1'
{
    if c == '1' then 1 else 0
}

method ParseLines(s: string) returns (lines: seq<seq<int>>)
    requires ValidInputString(s)
    ensures |lines| == 4
    ensures forall i :: 0 <= i < 4 ==> |lines[i]| == 4
    ensures forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> (lines[i][j] == 0 || lines[i][j] == 1)
{
    var result: seq<seq<int>> := [];
    var pos := 0;
    var lineCount := 0;
    
    while lineCount < 4
        invariant 0 <= pos <= |s|
        invariant |result| == lineCount
        invariant forall i :: 0 <= i < lineCount ==> |result[i]| == 4
        invariant forall i :: 0 <= i < lineCount ==> forall j :: 0 <= j < 4 ==> (result[i][j] == 0 || result[i][j] == 1)
        decreases 4 - lineCount, |s| - pos
    {
        var line: seq<int> := [];
        var intCount := 0;
        var posStart := pos;
        while intCount < 4 && pos < |s|
            invariant posStart <= pos <= |s|
            invariant |line| == intCount
            invariant forall j :: 0 <= j < intCount ==> (line[j] == 0 || line[j] == 1)
            decreases |s| - pos
        {
            if s[pos] == '0' || s[pos] == '1' {
                var v := if s[pos] == '1' then 1 else 0;
                line := line + [v];
                intCount := intCount + 1;
            }
            pos := pos + 1;
        }
        if |line| < 4 {
            line := line + [0, 0, 0, 0][|line|..];
        }
        result := result + [line];
        lineCount := lineCount + 1;
    }
    lines := result;
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] as int >= 0 && s[i] as int <= 127
    requires ValidInputString(s)
    ensures result == "YES\n" || result == "NO\n"
    ensures exists input_lines :: 
        ParseInput(s, input_lines) && 
        (result == "YES\n" <==> AccidentPossible(input_lines))
    ensures |result| >= 3
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): add assert to help Dafny prove AccidentAtLane equivalence */
    var lines := ParseLines(s);
    
    var accident := false;
    var i := 0;
    while i < 4
        invariant 0 <= i <= 4
        invariant accident <==> exists k :: 0 <= k < i && AccidentAtLane(k, lines)
    {
        var atLane :=
            (lines[i][3] == 1 && (lines[i][0] == 1 || lines[i][1] == 1 || lines[i][2] == 1)) ||
            (lines[i][0] == 1 && lines[(i + 3) % 4][3] == 1) ||
            (lines[i][1] == 1 && lines[(i + 2) % 4][3] == 1) ||
            (lines[i][2] == 1 && lines[(i + 1) % 4][3] == 1);
        assert atLane == AccidentAtLane(i, lines);
        if atLane {
            accident := true;
        }
        i := i + 1;
    }
    
    if accident {
        result := "YES\n";
    } else {
        result := "NO\n";
    }
    
    assert ParseInput(s, lines);
    if accident {
        assert AccidentPossible(lines);
    } else {
        assert !AccidentPossible(lines);
    }
}
// </vc-code>
