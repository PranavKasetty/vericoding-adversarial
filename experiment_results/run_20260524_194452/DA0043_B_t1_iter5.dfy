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
/* helper modified by LLM (iteration 5): fix proof of n%k<=0 for negative case */
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
    // n = x - k + 1, x < 0, so n <= x - k + 1 <= x
    // FloorDiv(x,k) = (x - k + 1) / k = n / k = q
    assert FloorDiv(x, k) == q;
    // For truncating division in Dafny: n == q * k + (n % k)
    // and -(k-1) <= n % k <= 0 when n < 0, k > 0
    // We know n % k satisfies: n == q * k + n % k
    // and 0 < k, n < 0 implies n % k in (-(k-1), 0]
    assert q * k + n % k == n;
    // Show n % k <= 0: since n < 0 and k > 0, truncating division rounds toward 0
    // q = n/k (truncating), so q <= 0 (since n < 0, k > 0)
    // n % k = n - q*k
    // q = n/k means q*k >= n (since truncating toward 0 for negatives means |q| <= |n/k|)
    assert n % k == n - q * k;
    // q*k <= 0 and n < 0; q*k >= n (truncating division property)
    assert q * k >= n by {
      // Dafny knows: for integer division, n == q*k + n%k, and |n%k| < k
      assert n % k > -k;
      assert n % k < k;
    }
    assert n % k <= 0 by {
      assert n % k == n - q * k;
      assert q * k >= n;
    }
    assert n % k > -k;
    // q*k = n - n%k
    // q*k <= x iff n - n%k <= x iff -k+1 - n%k <= 0 iff n%k >= 1-k iff n%k > -k ✓
    assert q * k == n - n % k;
    assert n == x - k + 1;
    assert q * k == x - k + 1 - n % k;
    assert q * k <= x by {
      assert n % k > -k;
    }
    assert x < (q + 1) * k by {
      assert n % k <= 0;
      assert (q + 1) * k == q * k + k;
      assert q * k == x - k + 1 - n % k;
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
  /* code modified by LLM (iteration 5): use monotonicity lemma to prove result >= 0 */
  FloorDivMonotone(a - 1, b, k);
  result := FloorDiv(b, k) - FloorDiv(a - 1, k);
}
// </vc-code>
