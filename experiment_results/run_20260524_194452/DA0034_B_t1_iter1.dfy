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
function {:fuel 200} simulateTrainsHelper(n: int, a: int, x: int, b: int, y: int, fuel: int): bool
  requires n >= 4
  requires 1 <= a <= n && 1 <= x <= n && 1 <= b <= n && 1 <= y <= n
  requires a != x && a != b && a != y && x != b && x != y && b != y
  decreases fuel
{
  if fuel == 0 then false
  else
    var a_next := if a % n + 1 == x then x
                  else if (a - 2 + n) % n + 1 == x then (a - 2 + n) % n + 1
                  else a % n + 1;
    var b_next := if b % n + 1 == y then y
                  else if (b - 2 + n) % n + 1 == y then (b - 2 + n) % n + 1
                  else b % n + 1;
    if a_next == b_next then true
    else if a_next == y && b_next == x then true
    else if a_next == b || b_next == a then true
    else
      var x_new := if a_next == x then (x % n + 1) else x;
      var y_new := if b_next == y then (y % n + 1) else y;
      if a_next == y_new || b_next == x_new then true
      else simulateTrainsHelper(n, a_next, x_new, b_next, y_new, fuel - 1)
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
  var parts := parseInput(stdin_input);
  var n := parts[0];
  var a := parts[1];
  var x := parts[2];
  var b := parts[3];
  var y := parts[4];
  if trainsWillMeet(stdin_input) {
    result := "YES\n";
  } else {
    result := "NO\n";
  }
}
// </vc-code>
