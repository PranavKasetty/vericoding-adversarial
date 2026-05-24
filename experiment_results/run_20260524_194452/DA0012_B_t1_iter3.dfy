// <vc-preamble>
predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0 &&
    (stdin_input[|stdin_input|-1] == '\n' || !('\n' in stdin_input))
}

predicate ValidResult(result: string)
{
    result == "BitAryo" || result == "BitLGM"
}

function GameResult(stdin_input: string): string
    requires ValidInput(stdin_input)
{
    var lines := splitLines(stdin_input);
    if |lines| >= 1 then
        var n := parseInt(lines[0]);
        if n == 3 && |lines| >= 2 then
            var values := parseInts(lines[1]);
            if |values| == 3 then
                var xorResult := xorSequence(values);
                if xorResult == 0 then "BitAryo" else "BitLGM"
            else "BitLGM"
        else if n == 2 && |lines| >= 2 then
            var values := parseInts(lines[1]);
            if |values| == 2 && values[0] >= 0 && values[1] >= 0 then
                var sortedValues := if values[0] <= values[1] then values else [values[1], values[0]];
                if goldenRatioRelation(sortedValues) then "BitAryo" else "BitLGM"
            else "BitLGM"
        else if |lines| >= 2 then
            var value := parseInt(lines[1]);
            if value == 0 then "BitAryo" else "BitLGM"
        else "BitLGM"
    else "BitLGM"
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed findNewline to use named return value */
function splitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var i := findNewline(s, 0);
        if i == |s| then [s]
        else [s[..i]] + splitLines(s[i+1..])
}

function findNewline(s: string, i: int): (r: int)
    requires 0 <= i <= |s|
    ensures i <= r <= |s|
    ensures r < |s| ==> s[r] == '\n'
    ensures r == |s| ==> forall j :: i <= j < |s| ==> s[j] != '\n'
    decreases |s| - i
{
    if i == |s| then i
    else if s[i] == '\n' then i
    else findNewline(s, i+1)
}

function parseInt(s: string): int
{
    parseIntHelper(s, 0, 0)
}

function parseIntHelper(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i == |s| then acc
    else if s[i] >= '0' && s[i] <= '9' then
        parseIntHelper(s, i+1, acc * 10 + (s[i] as int - '0' as int))
    else acc
}

function parseInts(s: string): seq<int>
{
    parseIntsHelper(s, 0, [], 0, false)
}

function parseIntsHelper(s: string, i: int, acc: seq<int>, cur: int, inNum: bool): seq<int>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        if inNum then acc + [cur] else acc
    else if s[i] >= '0' && s[i] <= '9' then
        parseIntsHelper(s, i+1, acc, cur * 10 + (s[i] as int - '0' as int), true)
    else if inNum then
        parseIntsHelper(s, i+1, acc + [cur], 0, false)
    else
        parseIntsHelper(s, i+1, acc, 0, false)
}

function xorSequence(values: seq<int>): int
{
    if |values| == 0 then 0
    else xorSequence(values[..|values|-1]) + values[|values|-1] - 2 * (xorSequence(values[..|values|-1]) * values[|values|-1] % 2)
}

function goldenRatioRelation(values: seq<int>): bool
    requires |values| == 2
{
    var a := values[0];
    var b := values[1];
    var diff := b - a;
    var k := diff;
    var floorKPhi := k + k * 1000 / 1618;
    a == floorKPhi
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures ValidResult(result)
    ensures result == GameResult(stdin_input)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implement solve using helper functions */
    var lines := splitLines(stdin_input);
    if |lines| >= 1 {
        var n := parseInt(lines[0]);
        if n == 3 && |lines| >= 2 {
            var values := parseInts(lines[1]);
            if |values| == 3 {
                var xorResult := xorSequence(values);
                if xorResult == 0 {
                    result := "BitAryo";
                } else {
                    result := "BitLGM";
                }
            } else {
                result := "BitLGM";
            }
        } else if n == 2 && |lines| >= 2 {
            var values := parseInts(lines[1]);
            if |values| == 2 && values[0] >= 0 && values[1] >= 0 {
                var sortedValues := if values[0] <= values[1] then values else [values[1], values[0]];
                if goldenRatioRelation(sortedValues) {
                    result := "BitAryo";
                } else {
                    result := "BitLGM";
                }
            } else {
                result := "BitLGM";
            }
        } else if |lines| >= 2 {
            var value := parseInt(lines[1]);
            if value == 0 {
                result := "BitAryo";
            } else {
                result := "BitLGM";
            }
        } else {
            result := "BitLGM";
        }
    } else {
        result := "BitLGM";
    }
}
// </vc-code>
