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
/* helper modified by LLM (iteration 2): removed duplicate parseInput declaration, kept full implementation */
function parseInput(input: string): seq<int>
  reads *
  requires |input| > 0
  requires exists i :: 0 <= i < |input| && input[i] == '\n'
{
  var i0 := skipNonDigits(input, 0);
  var (v0, i1) := parseNat(input, i0);
  var i2 := skipNonDigits(input, i1);
  var (v1, i3) := parseNat(input, i2);
  var i4 := skipNonDigits(input, i3);
  var (v2, i5) := parseNat(input, i4);
  var i6 := skipNonDigits(input, i5);
  var (v3, i7) := parseNat(input, i6);
  var i8 := skipNonDigits(input, i7);
  var (v4, _) := parseNat(input, i8);
  [v0, v1, v2, v3, v4]
}

predicate IsDigit(c: char)
{
  '0' <= c <= '9'
}

function charToInt(c: char): int
  requires IsDigit(c)
{
  (c as int) - ('0' as int)
}

function parseNat(s: string, i: int): (int, int)
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i >= |s| || !IsDigit(s[i]) then (0, i)
  else
    var (rest, j) := parseNat(s, i + 1);
    var digits := j - i;
    var multiplier := pow10(digits);
    (charToInt(s[i]) * multiplier + rest, j)
}

function pow10(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else 10 * pow10(n - 1)
}

function skipNonDigits(s: string, i: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i >= |s| || IsDigit(s[i]) then i
  else skipNonDigits(s, i + 1)
}

function nextPos(cur: int, dest: int, n: int): int
  requires n >= 1 && 1 <= cur <= n && 1 <= dest <= n
{
  if cur == dest then cur
  else if cur % n + 1 == dest then dest
  else cur % n + 1
}

function simulateTrainsHelper(n: int, a: int, x: int, b: int, y: int, fuel: int): bool
  requires n >= 4 && 1 <= a <= n && 1 <= x <= n && 1 <= b <= n && 1 <= y <= n
  requires a != x && a != b && a != y && x != b && x != y && b != y
  decreases fuel
{
  if fuel == 0 then false
  else
    var a' := nextPos(a, x, n);
    var b' := nextPos(b, y, n);
    if a' == b' then true
    else if a' == x && b' == y then false
    else simulateTrainsHelper(n, a', x, b', y, fuel - 1)
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
  /* code modified by LLM (iteration 2): implement solve using trainsWillMeet */
  var meets := trainsWillMeet(stdin_input);
  if meets {
    result := "YES\n";
  } else {
    result := "NO\n";
  }
}
// </vc-code>
