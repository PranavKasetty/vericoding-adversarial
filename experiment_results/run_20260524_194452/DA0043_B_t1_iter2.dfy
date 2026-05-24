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
/* helper modified by LLM (iteration 2): monotonicity lemma for FloorDiv */
lemma FloorDivMonotone(x: int, y: int, k: int)
  requires k > 0
  requires x <= y
  ensures FloorDiv(x, k) <= FloorDiv(y, k)
{
  // Key: FloorDiv(n, k) * k <= n < (FloorDiv(n, k) + 1) * k
  // From x <= y and these bounds, FloorDiv(x,k) <= FloorDiv(y,k)
  // We use the fact that FloorDiv computes mathematical floor division
  var fx := FloorDiv(x, k);
  var fy := FloorDiv(y, k);
  // Prove fx * k <= x
  if x >= 0 {
    assert fx == x / k;
    assert fx * k <= x;
  } else {
    assert fx == (x - k + 1) / k;
    // (x - k + 1) / k * k <= x - k + 1 + k - 1 = x
    assert fx * k <= x by {
      var q := (x - k + 1) / k;
      // q * k <= x - k + 1 + k - 1 in Dafny integer division
      // For negative numerator n, n/d rounds toward 0, so q*d >= n (since q is negative or zero and d > 0)
      // q = (x-k+1)/k, so q*k <= x-k+1 (since rounds toward 0 means |q*k| <= |x-k+1|)
      // Actually for negative: q*k >= x-k+1 (rounds toward 0), so q*k + k - 1 >= x, q*k >= x - k + 1
      // We need q*k <= x: q*k >= x-k+1, so q*k + k >= x+1, q*k >= x - k + 1. And q*k <= x because x-k+1 <= q*k+k-1+1... hmm
      assert (x - k + 1) / k * k <= x;
    }
  }
  // Prove y < (fy + 1) * k
  if y >= 0 {
    assert fy == y / k;
    assert y < (fy + 1) * k;
  } else {
    assert fy == (y - k + 1) / k;
    assert y < (fy + 1) * k;
  }
  // Now: fx * k <= x <= y < (fy+1)*k => fx <= fy
  assert fx * k <= x;
  assert y < (fy + 1) * k;
  assert fx * k <= y;
  assert fx * k < (fy + 1) * k;
  assert fx < fy + 1;
  assert fx <= fy;
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
  /* code modified by LLM (iteration 2): use monotonicity lemma to prove result >= 0 */
  FloorDivMonotone(a - 1, b, k);
  result := FloorDiv(b, k) - FloorDiv(a - 1, k);
}
// </vc-code>
