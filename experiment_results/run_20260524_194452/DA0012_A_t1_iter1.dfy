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
function splitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var i := findNewline(s, 0);
        if i == |s| then [s]
        else [s[..i]] + splitLines(s[i+1..])
}

function findNewline(s: string, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start == |s| then |s|
    else if s[start] == '\n' then start
    else findNewline(s, start + 1)
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
        parseIntHelper(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    else acc
}

function parseInts(s: string): seq<int>
{
    parseIntsHelper(s, 0)
}

function parseIntsHelper(s: string, i: int): seq<int>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then []
    else if s[i] == ' ' then parseIntsHelper(s, i + 1)
    else if s[i] >= '0' && s[i] <= '9' then
        var end := findNonDigit(s, i);
        var num := parseIntHelper(s, i, 0);
        [num] + parseIntsHelper(s, end)
    else parseIntsHelper(s, i + 1)
}

function findNonDigit(s: string, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start == |s| then |s|
    else if s[start] >= '0' && s[start] <= '9' then findNonDigit(s, start + 1)
    else start
}

function xorSequence(values: seq<int>): int
{
    if |values| == 0 then 0
    else xorBits(values[0], xorSequence(values[1..]))
}

function xorBits(a: int, b: int): int
{
    if a < 0 || b < 0 then 0
    else xorBitsHelper(a, b, 1)
}

function xorBitsHelper(a: int, b: int, place: int): int
    requires a >= 0 && b >= 0 && place >= 1
    decreases a + b
{
    if a == 0 && b == 0 then 0
    else
        var bitA := a % 2;
        var bitB := b % 2;
        var xorBit := if bitA != bitB then 1 else 0;
        xorBit * place + xorBitsHelper(a / 2, b / 2, place * 2)
}

function goldenRatioRelation(values: seq<int>): bool
    requires |values| == 2
{
    var a := values[0];
    var b := values[1];
    // Wythoff's game: losing positions are (floor(n*phi), floor(n*phi^2))
    // A position (a,b) with a<=b is losing iff b-a = floor((b-a)*phi) ... 
    // Actually: (a,b) is P-position iff a = floor(k*phi) and b = floor(k*phi^2) for some k
    // Equivalent: a = floor((b-a)*phi)
    // We use: a == floor((b-a) * 1.618...) which means a*10000 <= (b-a)*16180 < (a+1)*10000
    var diff := b - a;
    if diff < 0 then false
    else
        // Check if a == floor(diff * phi) where phi = (1+sqrt(5))/2
        // Use rational approximation: phi ~ 1597/987 (Fibonacci ratio)
        // a == floor(diff * 1597 / 987)
        // i.e., a * 987 <= diff * 1597 < (a+1) * 987
        a * 987 <= diff * 1597 && diff * 1597 < (a + 1) * 987
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
