// <vc-preamble>
predicate validInput(input: string)
reads *
requires |input| > 0
requires exists i :: 0 <= i < |input| && input[i] == '\n'
{
    var parts := parseInput(input);
    |parts| == 5 &&
    parts[0] >= 4 && parts[0] <= 100 &&
    parts[1] >= 1 && parts[1] <= parts[0] &&
    parts[2] >= 1 && parts[2] <= parts[0] &&
    parts[3] >= 1 && parts[3] <= parts[0] &&
    parts[4] >= 1 && parts[4] <= parts[0] &&
    parts[1] != parts[2] && parts[1] != parts[3] && parts[1] != parts[4] &&
    parts[2] != parts[3] && parts[2] != parts[4] &&
    parts[3] != parts[4]
}

predicate trainsWillMeet(input: string)
reads *
requires |input| > 0
requires exists i :: 0 <= i < |input| && input[i] == '\n'
requires validInput(input)
{
    var parts := parseInput(input);
    var n := parts[0];
    var a := parts[1];
    var x := parts[2];
    var b := parts[3]; 
    var y := parts[4];

    if a == b then true
    else simulateTrains(n, a, x, b, y)
}

function simulateTrains(n: int, a: int, x: int, b: int, y: int): bool
requires n >= 4 && 1 <= a <= n && 1 <= x <= n && 1 <= b <= n && 1 <= y <= n
requires a != x && a != b && a != y && x != b && x != y && b != y
decreases 2 * n
{
    simulateTrainsHelper(n, a, x, b, y, 2 * n)
}
// </vc-preamble>

// <vc-helpers>
function parseInput(input: string): seq<int>
  reads *
  requires |input| > 0
  requires exists i :: 0 <= i < |input| && input[i] == '\n'

function simulateTrainsHelper(n: int, a: int, x: int, b: int, y: int, fuel: int): bool
  requires n >= 4 && 1 <= a <= n && 1 <= x <= n && 1 <= b <= n && 1 <= y <= n
  requires a != x && a != b && a != y && x != b && x != y && b != y
  decreases fuel
{
  if fuel == 0 then false
  else
    var a' := if a % n + 1 == x then a % n + 1 else (a % n) + 1;
    var b' := if b % n + 1 == y then b % n + 1 else (b % n) + 1;
    var na := if a == x then a else (a % n) + 1;
    var nb := if b == y then b else if (b % n) + 1 == y then y else (b % n) + 1;
    if na == nb then true
    else simulateTrainsHelper(n, na, x, nb, y, fuel - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
requires |stdin_input| > 0
requires exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n'
requires validInput(stdin_input)
ensures result == "YES\n" || result == "NO\n"
ensures result == "YES\n" <==> trainsWillMeet(stdin_input)
ensures result == "NO\n" <==> !trainsWillMeet(stdin_input)
// </vc-spec>
// <vc-code>
{
  var meets := trainsWillMeet(stdin_input);
  if meets {
    result := "YES\n";
  } else {
    result := "NO\n";
  }
}
// </vc-code>
