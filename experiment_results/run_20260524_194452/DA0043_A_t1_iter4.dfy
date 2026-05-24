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
/* helper modified by LLM (iteration 4): non-recursive monotonicity proof */
lemma FloorDivMonotone(x: int, y: int, k: int)
  requires k > 0
  requires x <= y
  ensures FloorDiv(x, k) <= FloorDiv(y, k)
{
  if x >= 0 && y >= 0 {
    assert x / k <= y / k by {
      var dx := y - x;
      assert dx >= 0;
      assert y == x + dx;
      assert (x + dx) / k >= x / k by {
        NatDivMonotone(x, dx, k);
      }
    }
  } else if x < 0 && y < 0 {
    assert FloorDiv(x, k) == (x - k + 1) / k;
    assert FloorDiv(y, k) == (y - k + 1) / k;
    assert x - k + 1 <= y - k + 1;
    NegDivMonotone(x - k + 1, y - k + 1, k);
  } else if x < 0 && y >= 0 {
    assert FloorDiv(x, k) == (x - k + 1) / k;
    assert FloorDiv(y, k) == y / k;
    assert (x - k + 1) / k <= 0 by {
      assert x - k + 1 <= 0 - k + 1;
      assert 0 - k + 1 <= 0;
      assert x - k + 1 <= 0;
      NegDivNonPos(x - k + 1, k);
    }
    assert y / k >= 0;
  }
}

lemma NatDivMonotone(x: int, d: int, k: int)
  requires k > 0
  requires x >= 0
  requires d >= 0
  ensures (x + d) / k >= x / k
{
  assert (x + d) / k * k <= x + d;
  assert x / k * k <= x;
}

lemma NegDivMonotone(x: int, y: int, k: int)
  requires k > 0
  requires x <= y
  ensures x / k <= y / k
{
  assert y == x + (y - x);
  var d := y - x;
  assert d >= 0;
  if d == 0 {
  } else {
    assert x / k <= (x + d) / k by {
      assert x + d == y;
      assert x / k <= y / k by {
        assert y - x >= 1;
        assert x / k * k + (x % k) == x;
        assert y / k * k + (y % k) == y;
      }
    }
  }
}

lemma NegDivNonPos(x: int, k: int)
  requires k > 0
  requires x <= 0
  ensures x / k <= 0
{
  if x == 0 {
    assert x / k == 0;
  } else {
    assert x < 0;
    assert x / k < 0 || x / k == 0;
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
  /* code modified by LLM (iteration 4): compute result and use lemma for non-negativity */
  CountDivisiblesNonNeg(k, a, b);
  result := FloorDiv(b, k) - FloorDiv(a - 1, k);
}
// </vc-code>
