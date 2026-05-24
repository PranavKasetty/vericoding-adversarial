// <vc-preamble>
predicate IsValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 3 && 
    ParseInt(lines[0]) > 0 &&
    |ParseIntArray(lines[1])| == ParseInt(lines[0]) &&
    |ParseIntArray(lines[2])| == ParseInt(lines[0])
}

function GetInitialSum(input: string): int
    requires IsValidInput(input)
{
    var lines := SplitLines(input);
    Sum(ParseIntArray(lines[1]))
}

function GetTargetSum(input: string): int
    requires IsValidInput(input)
{
    var lines := SplitLines(input);
    Sum(ParseIntArray(lines[2]))
}

function Sum(nums: seq<int>): int
    decreases |nums|
{
    if |nums| == 0 then 0
    else nums[0] + Sum(nums[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed predicate syntax and added required helper functions */
function SplitLines(s: string): seq<string>
function ParseInt(s: string): int
function ParseIntArray(s: string): seq<int>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    ensures result == "Yes" || result == "No"
    ensures IsValidInput(input) ==> 
        (result == "Yes" <==> GetInitialSum(input) >= GetTargetSum(input))
    ensures !IsValidInput(input) ==> result == "No"
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed if-else syntax to use braces instead of then */
{
  if !IsValidInput(input) {
    result := "No";
  } else {
    var initialSum := GetInitialSum(input);
    var targetSum := GetTargetSum(input);
    if initialSum >= targetSum {
      result := "Yes";
    } else {
      result := "No";
    }
  }
}
// </vc-code>
