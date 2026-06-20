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
/* helper modified by LLM (iteration 3): monotonicity lemma for FloorDiv */
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
    // xn <= yn since x <= y
    assert xn <= yn;
    // xn / k <= yn / k
  } else {
    // x < 0 <= y
    assert x < 0;
    assert y >= 0;
    // FloorDiv(x,k) = (x-k+1)/k, FloorDiv(y,k) = y/k
    // (x-k+1) <= x < 0 <= y, and (x-k+1)/k <= 0 <= y/k for y >= 0... not necessarily
    // Need: (x-k+1)/k <= y/k
    // y/k >= 0 since y >= 0 and k > 0
    // (x-k+1)/k <= 0 since x < 0, so x-k+1 <= x < 0, so x-k+1 < 0, so (x-k+1)/k <= -1 < 0
    assert x - k + 1 < 0;
    var xn := x - k + 1;
    // xn < 0, k > 0, so in Dafny Euclidean: xn / k <= -1 < 0 <= y / k
    assert xn / k <= -1 by {
      // xn < 0 and k > 0: xn / k = floor(xn/k) <= -1
      var q := xn / k;
      var r := xn % k;
      assert xn == q * k + r;
      assert 0 <= r < k;
      // xn < 0, r >= 0, so q*k = xn - r < 0, so q < 0, so q <= -1
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
  /* code modified by LLM (iteration 3): use monotonicity lemma to prove non-negativity */
  FloorDivMonotone(a - 1, b, k);
  result := FloorDiv(b, k) - FloorDiv(a - 1, k);
}
// </vc-code>
