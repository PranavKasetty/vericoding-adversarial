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
    if c == '0' then 0 else 1
}

function ParseGridFromString(s: string): seq<seq<int>>
    requires ValidInputString(s)
    ensures |ParseGridFromString(s)| == 4
    ensures forall i :: 0 <= i < 4 ==> |ParseGridFromString(s)[i]| == 4
    ensures forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> 
        (ParseGridFromString(s)[i][j] == 0 || ParseGridFromString(s)[i][j] == 1)
{
    // We rely on AllLinesHaveFourValidIntegers: all chars are 0,1,space,newline
    // We'll extract bits from positions, finding lines separated by newlines
    // Find first line's bits (first 4 bits among chars that are 0 or 1)
    var bits := ExtractBits(s);
    if |bits| < 16 then
        [[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]
    else
        [[bits[0],bits[1],bits[2],bits[3]],
         [bits[4],bits[5],bits[6],bits[7]],
         [bits[8],bits[9],bits[10],bits[11]],
         [bits[12],bits[13],bits[14],bits[15]]]
}

function ExtractBits(s: string): seq<int>
    requires forall i :: 0 <= i < |s| ==> (s[i] == '0' || s[i] == '1' || s[i] == ' ' || s[i] == '\n')
    ensures forall i :: 0 <= i < |ExtractBits(s)| ==> (ExtractBits(s)[i] == 0 || ExtractBits(s)[i] == 1)
{
    if |s| == 0 then []
    else if s[0] == '0' then [0] + ExtractBits(s[1..])
    else if s[0] == '1' then [1] + ExtractBits(s[1..])
    else ExtractBits(s[1..])
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
    var bits := ExtractBits(s);
    var grid: seq<seq<int>>;
    if |bits| < 16 {
        grid := [[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]];
    } else {
        grid := [[bits[0],bits[1],bits[2],bits[3]],
                 [bits[4],bits[5],bits[6],bits[7]],
                 [bits[8],bits[9],bits[10],bits[11]],
                 [bits[12],bits[13],bits[14],bits[15]]];
    }
    
    // Check accident possible
    var accident := false;
    var i := 0;
    while i < 4
        invariant 0 <= i <= 4
        invariant accident ==> AccidentPossible(grid)
    {
        var lane := grid[i];
        var prevLane := grid[(i + 3) % 4];
        var prevLane2 := grid[(i + 2) % 4];
        var prevLane3 := grid[(i + 1) % 4];
        
        if lane[3] == 1 && (lane[0] == 1 || lane[1] == 1 || lane[2] == 1) {
            accident := true;
        }
        if lane[0] == 1 && prevLane[3] == 1 {
            accident := true;
        }
        if lane[1] == 1 && prevLane2[3] == 1 {
            accident := true;
        }
        if lane[2] == 1 && prevLane3[3] == 1 {
            accident := true;
        }
        i := i + 1;
    }
    
    var input_lines := grid;
    assert ParseInput(s, input_lines) by {
        assert |input_lines| == 4;
        assert forall ii :: 0 <= ii < 4 ==> |input_lines[ii]| == 4;
        assert forall ii :: 0 <= ii < 4 ==> forall jj :: 0 <= jj < 4 ==> 
            (input_lines[ii][jj] >= 0 && input_lines[ii][jj] <= 1);
        assert StringContainsFourLinesOfFourIntegers(s, input_lines);
    }
    
    if accident {
        assert AccidentPossible(input_lines);
        result := "YES\n";
    } else {
        assert !AccidentPossible(input_lines) by {
            forall ii | 0 <= ii < 4 ensures !AccidentAtLane(ii, input_lines) {
                var l := input_lines[ii];
                var p1 := input_lines[(ii + 3) % 4];
                var p2 := input_lines[(ii + 2) % 4];
                var p3 := input_lines[(ii + 1) % 4];
                assert !(l[3] == 1 && (l[0] == 1 || l[1] == 1 || l[2] == 1));
                assert !(l[0] == 1 && p1[3] == 1);
                assert !(l[1] == 1 && p2[3] == 1);
                assert !(l[2] == 1 && p3[3] == 1);
            }
        }
        result := "NO\n";
    }
}
// </vc-code>
