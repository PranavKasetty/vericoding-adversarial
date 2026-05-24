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
/* helper modified by LLM (iteration 2): lemma proving FloorDiv is monotone */
lemma FloorDivMonotone(x: int, y: int, k: int)
  requires k > 0
  requires x <= y
  ensures FloorDiv(x, k) <= FloorDiv(y, k)
{
  if x >= 0 && y >= 0 {
    // Both non-negative: x/k <= y/k by integer division monotonicity
    assert x / k <= y / k;
  } else if x < 0 && y < 0 {
    // Both negative: (x - k + 1)/k <= (y - k + 1)/k
    assert (x - k + 1) / k <= (y - k + 1) / k;
  } else {
    // x < 0 <= y
    // FloorDiv(x, k) = (x - k + 1) / k < 0 <= 0 <= y / k = FloorDiv(y, k)
    assert x < 0;
    assert y >= 0;
    // (x - k + 1) <= x <= -1 < 0, so (x - k + 1) / k <= -1 < 0 <= y / k
    var num := x - k + 1;
    assert num <= x - k + 1;
    assert num < 0;
    // num / k when num < 0 and k > 0: result is <= -1
    assert num / k <= 0;
    assert y / k >= 0;
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
  /* code modified by LLM (iteration 2): compute result and use lemma for non-negativity */
  CountDivisiblesNonNeg(k, a, b);
  result := FloorDiv(b, k) - FloorDiv(a - 1, k);
}
// </vc-code>
