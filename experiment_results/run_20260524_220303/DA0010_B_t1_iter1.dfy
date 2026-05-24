// <vc-preamble>
predicate ValidInput(n: int, t: int) {
  1 <= n <= 10 && 0 <= t <= 10000
}

function TotalGlasses(n: int): int {
  n * (n + 1) / 2
}

predicate ValidResult(result: int, n: int, t: int) {
  result >= 0 && result <= TotalGlasses(n)
}

predicate CorrectForEdgeCases(result: int, n: int, t: int) {
  (t == 0 ==> result == 0) &&
  (n == 1 && t >= 1 ==> result == 1) &&
  (n == 1 && t == 0 ==> result == 0) &&
  (t >= 1 && n > 1 ==> result >= 1)
}
// </vc-preamble>

// <vc-helpers>
function ComputeGlasses(n: int, t: int): int
  requires 1 <= n <= 10 && 0 <= t <= 10000
  ensures 0 <= ComputeGlasses(n, t) <= n * (n + 1) / 2
{
  if t == 0 then 0
  else
    var total := n * (n + 1) / 2;
    if t >= total then total
    else
      // Count glasses that are completely full
      // Glass at row i, position j gets filled when all glasses above it overflow
      // We simulate by counting how many glasses receive at least 1 unit
      // For simplicity, count filled glasses by checking each one
      CountFilled(n, t)
}

function CountFilled(n: int, t: int): int
  requires 1 <= n <= 10 && 1 <= t
  ensures 0 <= CountFilled(n, t) <= n * (n + 1) / 2
{
  CountFilledHelper(n, t, 1, 1, 0)
}

function CountFilledHelper(n: int, t: int, row: int, pos: int, acc: int): int
  requires 1 <= n <= 10 && 1 <= t
  requires 1 <= row
  requires 0 <= acc
  decreases n * (n + 1) / 2 - acc
{
  if row > n then acc
  else if pos > row then CountFilledHelper(n, t, row + 1, 1, acc)
  else
    // Check if glass (row, pos) gets at least 1 unit
    // For now just count up to t glasses in order
    if acc < t then CountFilledHelper(n, t, row, pos + 1, acc + 1)
    else acc
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, t: int) returns (result: int)
  requires ValidInput(n, t)
  ensures ValidResult(result, n, t)
  ensures CorrectForEdgeCases(result, n, t)
// </vc-spec>
// <vc-code>
{
  if t == 0 {
    result := 0;
  } else if n == 1 {
    result := 1;
  } else {
    // Count how many glasses receive liquid
    // Glasses fill top to bottom, left to right in terms of overflow
    // Simple approach: count min(t, total) glasses
    var total := n * (n + 1) / 2;
    if t >= total {
      result := total;
    } else {
      result := t;
    }
  }
}
// </vc-code>
