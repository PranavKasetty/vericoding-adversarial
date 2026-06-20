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
/* helper modified by LLM (iteration 4): monotonicity lemma for FloorDiv with complete proof for negative case */
lemma FloorDivMonotone(x: int, y: int, k: int)
  requires k > 0
  requires x <= y
  ensures FloorDiv(x, k) <= FloorDiv(y, k)
{
  if x >= 0 && y >= 0 {
    // Both non-negative: x/k <= y/k by Dafny's division monotonicity
  } else if x < 0 && y < 0 {
    // Both negative
    var xn := x - k + 1;
    var yn := y - k + 1;
    assert xn <= yn;
    // Need to show xn / k <= yn / k
    // Use the fact that for integers p <= q, p/k <= q/k when k > 0
    // We'll prove this by showing yn - xn >= 0 and using modular arithmetic
    var diff := yn - xn;
    assert diff == y - x;
    assert diff >= 0;
    // yn = xn + diff, so yn / k = (xn + diff) / k >= xn / k
    // Proof: yn / k - xn / k = (xn + diff) / k - xn / k >= 0
    // since xn / k + diff / k <= (xn + diff) / k ... need careful reasoning
    // Instead, use: xn % k + (yn - xn) + (xn / k)*k = yn, so yn / k = xn/k + something >= 0
    var qx := xn / k;
    var rx := xn % k;
    assert xn == qx * k + rx;
    assert 0 <= rx < k;
    // yn = xn + diff = qx*k + rx + diff
    assert yn == qx * k + rx + diff;
    // yn / k = qx + (rx + diff) / k
    assert yn / k == qx + (rx + diff) / k by {
      assert yn == qx * k + (rx + diff);
      assert yn / k == qx + (rx + diff) / k by {
        var total := rx + diff;
        assert total >= 0;
        assert yn == qx * k + total;
        // In Dafny, (a*k + b) / k == a + b/k when b >= 0
        calc {
          yn / k;
          == (qx * k + total) / k;
          == qx + total / k;
        }
      }
    }
    assert (rx + diff) / k >= 0;
    assert yn / k >= qx;
    assert yn / k >= xn / k;
  } else {
    // x < 0 <= y
    assert x < 0;
    assert y >= 0;
    var xn := x - k + 1;
    assert xn < 0;
    assert xn / k <= -1 by {
      var q := xn / k;
      var r := xn % k;
      assert xn == q * k + r;
      assert 0 <= r < k;
      if q >= 0 {
        assert q * k >= 0;
        assert xn == q * k + r >= 0;
        assert false;
      }
    }
    assert y / k >= 0;
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
  /* code modified by LLM (iteration 4): use monotonicity lemma to prove non-negativity */
  FloorDivMonotone(a - 1, b, k);
  result := FloorDiv(b, k) - FloorDiv(a - 1, k);
}
// </vc-code>
