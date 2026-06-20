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
/* helper modified by LLM (iteration 5): simplified monotonicity lemma to avoid timeout */
lemma FloorDivMonotone(x: int, y: int, k: int)
  requires k > 0
  requires x <= y
  ensures FloorDiv(x, k) <= FloorDiv(y, k)
{
  if x >= 0 {
    if y >= 0 {
      // Both non-negative
    } else {
      assert false; // y >= x >= 0 so y >= 0
    }
  } else if y >= 0 {
    // x < 0 <= y
    var xn := x - k + 1;
    assert xn <= x < 0;
    assert xn < 0;
    assert FloorDiv(x, k) == xn / k;
    assert FloorDiv(y, k) == y / k;
    assert y / k >= 0;
    assert xn / k < 0 by {
      assert xn < 0;
      assert k > 0;
      var q := xn / k;
      var r := xn % k;
      assert xn == q * k + r && 0 <= r < k;
      if q >= 0 { assert q * k + r >= 0; assert xn >= 0; assert false; }
    }
  } else {
    // Both negative: x <= y < 0
    assert x < 0 && y < 0;
    var xn := x - k + 1;
    var yn := y - k + 1;
    assert xn <= yn;
    assert FloorDiv(x, k) == xn / k;
    assert FloorDiv(y, k) == yn / k;
    // Show xn/k <= yn/k where xn <= yn
    // yn = xn + (yn - xn), yn - xn = y - x >= 0
    var d := yn - xn;
    assert d >= 0;
    var q := xn / k;
    var r := xn % k;
    assert xn == q * k + r && 0 <= r < k;
    assert yn == q * k + r + d;
    assert r + d >= 0;
    assert yn / k == q + (r + d) / k by {
      assert yn == q * k + (r + d);
      assert r + d >= 0;
    }
    assert (r + d) / k >= 0;
    assert yn / k >= q;
    assert yn / k >= xn / k;
  }
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
  /* code modified by LLM (iteration 5): use monotonicity lemma to prove non-negativity */
  FloorDivMonotone(a - 1, b, k);
  result := FloorDiv(b, k) - FloorDiv(a - 1, k);
}
// </vc-code>
