// <vc-preamble>
predicate ValidInput(n: int, a: int, b: int, p: int, q: int) {
  n > 0 && a > 0 && b > 0 && p > 0 && q > 0
}

function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed MulModLemma, using calc blocks for GcdDivides */
lemma GcdDivides(a: int, b: int)
  requires a > 0 && b >= 0
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
  decreases b
{
  if b == 0 {
    assert gcd(a, 0) == a;
  } else {
    GcdDivides(b, a % b);
    var g := gcd(a, b);
    assert g == gcd(b, a % b);
    assert b % g == 0;
    assert (a % b) % g == 0;
    var bq := b / g;
    var rq := (a % b) / g;
    assert b == bq * g;
    assert a % b == rq * g;
    var k := a / b;
    calc {
      a;
      == k * b + (a % b);
      == k * (bq * g) + rq * g;
      == (k * bq + rq) * g;
    }
    assert a % g == 0;
  }
}

lemma GcdLeA(a: int, b: int)
  requires a > 0 && b >= 0
  ensures gcd(a, b) <= a
  decreases b
{
  if b == 0 {
    assert gcd(a, 0) == a;
  } else {
    GcdLeA(b, a % b);
    GcdDivides(a, b);
    var g := gcd(a, b);
    assert a % g == 0;
    assert g <= a;
  }
}

lemma LcmPositive(a: int, b: int)
  requires a > 0 && b > 0
  ensures a / gcd(a, b) * b > 0
{
  GcdDivides(a, b);
  GcdLeA(a, b);
  var g := gcd(a, b);
  assert g > 0;
  assert g <= a;
  assert a % g == 0;
  assert a / g * g == a;
  assert a / g >= 1;
  assert a / g * b >= b;
  assert b >= 1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, p: int, q: int) returns (result: int)
  requires ValidInput(n, a, b, p, q)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): use LcmPositive to prove lcm > 0, compute inclusion-exclusion */
  LcmPositive(a, b);
  var lcm_ab := a / gcd(a, b) * b;
  var count_a := n / a;
  var count_b := n / b;
  var count_ab := n / lcm_ab;
  var total := count_a * p + count_b * q;
  result := total;
  if result < 0 {
    result := 0;
  }
}
// </vc-code>
