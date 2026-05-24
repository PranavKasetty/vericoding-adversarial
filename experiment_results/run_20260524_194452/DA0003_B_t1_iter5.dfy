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
/* helper modified by LLM (iteration 5): simplified lemmas to avoid timeouts */
lemma GcdDividesA(a: int, b: int)
  requires a > 0 && b > 0
  ensures a % gcd(a, b) == 0
  decreases b
{
  var r := a % b;
  if r == 0 {
    assert gcd(a, b) == b;
    assert a % b == 0;
  } else {
    GcdDividesA(b, r);
    var g := gcd(b, r);
    assert b % g == 0;
    assert r % g == 0;
    assert a % b == r;
    assert a == b * (a / b) + r;
    assert a % g == (b * (a / b) % g + r % g) % g;
    assert b % g == 0;
    assert (b * (a / b)) % g == 0;
    assert r % g == 0;
    assert a % g == 0;
    assert gcd(a, b) == g;
  }
}

lemma LcmPositive(a: int, b: int)
  requires a > 0 && b > 0
  ensures (a * b) / gcd(a, b) >= 1
{
  GcdDividesA(a, b);
  var g := gcd(a, b);
  assert g > 0;
  assert a % g == 0;
  var k := a / g;
  assert k >= 1;
  assert a == g * k;
  assert a * b == g * k * b;
  assert g * k * b == g * (k * b);
  assert (g * (k * b)) / g == k * b by {
    assert g * (k * b) / g == k * b;
  }
  assert (a * b) / g == k * b;
  assert k * b >= 1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, p: int, q: int) returns (result: int)
  requires ValidInput(n, a, b, p, q)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): simplified solve */
  GcdDividesA(a, b);
  var g := gcd(a, b);
  assert g > 0;
  assert a % g == 0;
  var k := a / g;
  assert k >= 1;
  assert a == g * k;
  assert a * b == g * k * b;
  assert g * k * b == g * (k * b);
  assert (g * (k * b)) / g == k * b;
  var lcm := k * b;
  assert lcm >= 1;
  var full_cycles := n / lcm;
  var remainder := n % lcm;
  var base_cost := full_cycles * (p + q);
  assert full_cycles >= 0;
  assert base_cost >= 0;
  var extra_cost := 0;
  if remainder >= a && remainder >= b {
    extra_cost := p + q;
  } else if remainder >= a {
    extra_cost := p;
  } else if remainder >= b {
    extra_cost := q;
  }
  result := base_cost + extra_cost;
  assert result >= 0;
}
// </vc-code>
