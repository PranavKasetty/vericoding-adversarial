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
/* helper modified by LLM (iteration 3): fixed proof of y < (fy+1)*k in negative branch */
lemma FloorDivMonotone(x: int, y: int, k: int)
  requires k > 0
  requires x <= y
  ensures FloorDiv(x, k) <= FloorDiv(y, k)
{
  var fx := FloorDiv(x, k);
  var fy := FloorDiv(y, k);
  if x >= 0 {
    assert fx == x / k;
    assert fx * k <= x;
  } else {
    assert fx == (x - k + 1) / k;
    assert (x - k + 1) / k * k >= x - k + 1;
    assert fx * k >= x - k + 1;
    assert fx * k <= x by {
      assert fx * k + (k - 1) >= x;
      assert fx * k <= x;
    }
  }
  if y >= 0 {
    assert fy == y / k;
    assert y < (fy + 1) * k;
  } else {
    assert fy == (y - k + 1) / k;
    var n := y - k + 1;
    assert n < 0;
    assert n / k * k >= n by {
      assert (y - k + 1) / k * k >= y - k + 1;
    }
    assert fy * k >= y - k + 1;
    assert fy * k + k >= y + 1;
    assert (fy + 1) * k >= y + 1;
    assert y < (fy + 1) * k;
  }
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
  /* code modified by LLM (iteration 3): use monotonicity lemma to prove result >= 0 */
  FloorDivMonotone(a - 1, b, k);
  result := FloorDiv(b, k) - FloorDiv(a - 1, k);
}
// </vc-code>
