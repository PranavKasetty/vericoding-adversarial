// <vc-preamble>
function countNewlines(s: string): int
{
    if |s| == 0 then 0
    else (if s[0] == '\n' then 1 else 0) + countNewlines(s[1..])
}

predicate ValidInput(input: string)
{
    |input| > 0 && '\n' in input && countNewlines(input) >= 3
}

function extractAndNormalizePuzzle1(input: string): string
    requires ValidInput(input)
{
    var lines := splitLines(input);
    if |lines| >= 2 then
        var line1 := lines[0];
        var line2 := reverse(lines[1]);
        var combined := line1 + line2;
        removeFirstX(combined)
    else
        ""
}

function extractAndNormalizePuzzle2(input: string): string
    requires ValidInput(input)
{
    var lines := splitLines(input);
    if |lines| >= 4 then
        var line3 := lines[2];
        var line4 := reverse(lines[3]);
        var combined := line3 + line4;
        removeFirstX(combined)
    else
        ""
}

predicate CanReachSameConfig(input: string)
    requires ValidInput(input)
{
    exists rotation :: 0 <= rotation < 4 && 
        extractAndNormalizePuzzle1(input) == rotatePuzzleLeft(extractAndNormalizePuzzle2(input), rotation)
}
// </vc-preamble>

// <vc-helpers>
function splitLines(s: string): seq<string>
{
    if |s| == 0 then [""]
    else if s[0] == '\n' then [""] + splitLines(s[1..])
    else
        var rest := splitLines(s[1..]);
        if |rest| == 0 then [[s[0]]]
        else [[s[0]] + rest[0]] + rest[1..]
}

function reverse(s: string): string
{
    if |s| == 0 then ""
    else reverse(s[1..]) + [s[0]]
}

function removeFirstX(s: string): string
{
    if |s| == 0 then ""
    else if s[0] == 'X' || s[0] == 'x' then s[1..]
    else s
}

function rotatePuzzleLeft(s: string, n: int): string
    requires 0 <= n < 4
{
    if n == 0 then s
    else if n == 1 then if |s| == 0 then s else s[1..] + [s[0]]
    else if n == 2 then if |s| <= 1 then s else s[2..] + s[..2]
    else if |s| <= 2 then s else s[3..] + s[..3]
}

lemma CanReachDecide(input: string) returns (b: bool)
    requires ValidInput(input)
    ensures b <==> CanReachSameConfig(input)
{
    var p1 := extractAndNormalizePuzzle1(input);
    var p2 := extractAndNormalizePuzzle2(input);
    if p1 == rotatePuzzleLeft(p2, 0) {
        b := true;
        assert 0 <= 0 < 4;
    } else if p1 == rotatePuzzleLeft(p2, 1) {
        b := true;
        assert 0 <= 1 < 4;
    } else if p1 == rotatePuzzleLeft(p2, 2) {
        b := true;
        assert 0 <= 2 < 4;
    } else if p1 == rotatePuzzleLeft(p2, 3) {
        b := true;
        assert 0 <= 3 < 4;
    } else {
        b := false;
        forall r | 0 <= r < 4 ensures p1 != rotatePuzzleLeft(p2, r) {
            if r == 0 { assert p1 != rotatePuzzleLeft(p2, 0); }
            else if r == 1 { assert p1 != rotatePuzzleLeft(p2, 1); }
            else if r == 2 { assert p1 != rotatePuzzleLeft(p2, 2); }
            else { assert p1 != rotatePuzzleLeft(p2, 3); }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == "YES\n" || result == "NO\n"
    ensures result == "YES\n" <==> CanReachSameConfig(input)
// </vc-spec>
// <vc-code>
{
    var b := CanReachDecide(input);
    if b {
        result := "YES\n";
    } else {
        result := "NO\n";
    }
}
// </vc-code>
