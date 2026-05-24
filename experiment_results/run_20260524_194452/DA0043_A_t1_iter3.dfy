// <vc-preamble>
predicate ValidInput(k: int, a: int, b: int)
{
  k > 0 && a <= b
}

function FloorDiv(a: int, b: int): int
  requires b > 0
{
  if a >= 0 then a / b
  else (a - b + 1) / b
}

function CountDivisiblesInRange(k: int, a: int, b: int): int
  requires k > 0
  requires a <= b
{
  FloorDiv(b, k) - FloorDiv(a - 1, k)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simplified monotonicity proof to avoid timeout */
lemma FloorDivMonotone(x: int, y: int, k: int)
  requires k > 0
  requires x <= y
  ensures FloorDiv(x, k) <= FloorDiv(y, k)
  decreases y - x
{
  if x == y {
    // trivial
  } else {
    // x < y, so x <= y - 1
    FloorDivMonotone(x, y - 1, k);
    // Now show FloorDiv(y-1, k) <= FloorDiv(y, k)
    if (y - 1) >= 0 {
      assert y >= 1;
      assert (y - 1) / k <= y / k;
    } else if y >= 0 {
      // y - 1 < 0 <= y means y == 0
      assert y == 0;
      // FloorDiv(-1, k) = (-1 - k + 1)/k = (-k)/k = -1
      assert (-1 - k + 1) / k == -1;
      assert FloorDiv(-1, k) == -1;
      assert FloorDiv(0, k) == 0;
    } else {
      // both negative
      assert y < 0;
      assert y - 1 < 0;
      assert (y - 1 - k + 1) / k <= (y - k + 1) / k;
    }
  }
}

lemma CountDivisiblesNonNeg(k: int, a: int, b: int)
  requires k > 0
  requires a <= b
  ensures CountDivisiblesInRange(k, a, b) >= 0
{
  FloorDivMonotone(a - 1, b, k);
}
// </vc-helpers>

// <vc-spec>
method solve(k: int, a: int, b: int) returns (result: int)
  requires ValidInput(k, a, b)
  ensures result >= 0
  ensures result == CountDivisiblesInRange(k, a, b)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): compute result and use lemma for non-negativity */
  CountDivisiblesNonNeg(k, a, b);
  result := FloorDiv(b, k) - FloorDiv(a - 1, k);
}
// </vc-code>
