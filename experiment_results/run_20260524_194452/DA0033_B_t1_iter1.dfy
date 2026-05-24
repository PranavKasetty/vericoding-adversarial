// <vc-preamble>
function CountDistinct(s: string): int
{
    |set c | 0 <= c < |s| :: s[c]|
}

predicate ValidInput(input: string)
{
    |input| > 0 &&
    input[|input|-1] == '\n' &&
    |input| >= 2 &&
    forall i :: 0 <= i < |input|-1 ==> 'a' <= input[i] <= 'z'
}

predicate CorrectOutput(username: string, output: string)
{
    var distinctCount := CountDistinct(username);
    (distinctCount % 2 == 1 ==> output == "IGNORE HIM!\n") &&
    (distinctCount % 2 == 0 ==> output == "CHAT WITH HER!\n")
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures var username := input[..|input|-1];
            CorrectOutput(username, output)
// </vc-spec>
// <vc-code>
{
  var username := input[..|input|-1];
  var n := |username|;
  var chars: set<char> := {};
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant chars == set c | 0 <= c < i :: username[c]
  {
    chars := chars + {username[i]};
    i := i + 1;
  }
  assert chars == set c | 0 <= c < |username| :: username[c];
  var distinctCount := |chars|;
  assert distinctCount == CountDistinct(username);
  if distinctCount % 2 == 1 {
    output := "IGNORE HIM!\n";
  } else {
    output := "CHAT WITH HER!\n";
  }
}
// </vc-code>
