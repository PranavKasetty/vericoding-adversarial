// <vc-preamble>
function Max3(a: int, b: int, c: int): int
{
    if a >= b && a >= c then a
    else if b >= c then b
    else c
}

function CalculateMissedMeals(input: string): int
{
    var parts := SplitSpaces(TrimNewline(input));
    if |parts| >= 3 then
        var a := StringToInt(parts[0]);
        var b := StringToInt(parts[1]);  
        var c := StringToInt(parts[2]);
        var maxVal := Max3(a, b, c);
        var threshold := maxVal - 1;
        (if a < threshold then threshold - a else 0) +
        (if b < threshold then threshold - b else 0) +
        (if c < threshold then threshold - c else 0)
    else 0
}

predicate ValidInput(input: string)
{
    |input| > 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): declare external string utility functions */
function TrimNewline(s: string): string
function SplitSpaces(s: string): seq<string>
function StringToInt(s: string): int
function IntToString(n: int): string
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
requires ValidInput(input)
ensures result == IntToString(CalculateMissedMeals(input))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implement solve using helper functions */
{
  var parts := SplitSpaces(TrimNewline(input));
  if |parts| >= 3 {
    var a := StringToInt(parts[0]);
    var b := StringToInt(parts[1]);
    var c := StringToInt(parts[2]);
    var maxVal := Max3(a, b, c);
    var threshold := maxVal - 1;
    var missed := (if a < threshold then threshold - a else 0) +
                  (if b < threshold then threshold - b else 0) +
                  (if c < threshold then threshold - c else 0);
    result := IntToString(missed);
  } else {
    result := IntToString(0);
  }
}
// </vc-code>
