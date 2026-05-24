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
/* helper modified by LLM (iteration 4): clean proof using floor bounds lemma */
lemma FloorDivBounds(x: int, k: int)
  requires k > 0
  ensures FloorDiv(x, k) * k <= x
  ensures x < (FloorDiv(x, k) + 1) * k
{
  if x >= 0 {
    var q := x / k;
    assert q * k <= x < (q + 1) * k by {
      assert q * k + x % k == x;
      assert x % k >= 0;
      assert x % k < k;
    }
  } else {
    var n := x - k + 1;
    var q := n / k;
    // n <= x < 0, k > 0
    // For Dafny truncating division: n == q * k + n % k
    // n < 0, so n % k <= 0
    assert n % k <= 0 by {
      assert n * k <= 0;
    }
    assert q * k + n % k == n;
    assert n % k <= 0;
    assert n % k > -k;
    // q * k = n - n%k >= n (since n%k <= 0)
    assert q * k >= n;
    assert q * k <= x by {
      assert q * k >= x - k + 1;
      assert q * k >= x - k + 1;
      // We need q*k <= x
      // q*k >= x - k + 1, and q*k = n - n%k = (x-k+1) - n%k
      // = x - k + 1 - n%k
      // n%k <= 0, so -n%k >= 0, so q*k = x - k + 1 - n%k >= x - k + 1
      // But we need q*k <= x
      // q*k = x - k + 1 - n%k
      // Need: x - k + 1 - n%k <= x
      // i.e., -k + 1 - n%k <= 0
      // i.e., n%k >= 1 - k
      // i.e., n%k > -k, which is true
      assert -k < n % k;
      assert q * k == n - n % k;
      assert n == x - k + 1;
      assert q * k == x - k + 1 - n % k;
      assert n % k > -k;
      assert -n % k < k;
      assert q * k < x + 1;
    }
    assert x < (q + 1) * k by {
      assert q * k == x - k + 1 - n % k;
      assert n % k <= 0;
      assert q * k >= x - k + 1;
      assert (q + 1) * k >= x + 1;
    }
  }
}

lemma FloorDivMonotone(x: int, y: int, k: int)
  requires k > 0
  requires x <= y
  ensures FloorDiv(x, k) <= FloorDiv(y, k)
{
  FloorDivBounds(x, k);
  FloorDivBounds(y, k);
  var fx := FloorDiv(x, k);
  var fy := FloorDiv(y, k);
  assert fx * k <= x;
  assert y < (fy + 1) * k;
  assert fx * k <= y;
  assert fx * k < (fy + 1) * k;
  assert fx < fy + 1;
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
  /* code modified by LLM (iteration 4): use monotonicity lemma to prove result >= 0 */
  FloorDivMonotone(a - 1, b, k);
  result := FloorDiv(b, k) - FloorDiv(a - 1, k);
}
// </vc-code>
