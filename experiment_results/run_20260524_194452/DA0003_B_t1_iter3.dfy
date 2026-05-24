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
/* helper modified by LLM (iteration 3): add lemma proving lcm is positive */
lemma GcdDividesProduct(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) <= a
  ensures (a * b) / gcd(a, b) > 0
{
  var g := gcd(a, b);
  assert g > 0;
  assert g <= a by {
    // gcd(a,b) divides a, so gcd(a,b) <= a
    var k := a / g;
    var r := a % g;
    // We need to show g <= a
    // Since g divides a and a > 0, g <= a
    GcdDividesA(a, b);
  }
  assert (a * b) / g >= b by {
    GcdDividesA(a, b);
    var k := a / g;
    assert a == g * k;
    assert (a * b) / g == (g * k * b) / g == k * b;
    assert k >= 1;
    assert k * b >= b;
  }
  assert (a * b) / g >= 1;
}

lemma GcdDividesA(a: int, b: int)
  requires a > 0 && b > 0
  ensures a % gcd(a, b) == 0
  decreases b
{
  if b == a {
    assert gcd(a, b) == gcd(a, a);
    assert a % a == 0;
    assert gcd(a, a) == a;
  } else if a % b == 0 {
    assert gcd(a, b) == gcd(b, a % b) == gcd(b, 0) == b;
    assert a % b == 0;
  } else {
    // gcd(a, b) == gcd(b, a % b)
    // By induction, b % gcd(b, a%b) == 0 and (a%b) % gcd(b,a%b) == 0
    // gcd(a,b) divides a = b*(a/b) + (a%b)
    var r := a % b;
    var q := a / b;
    assert a == b * q + r;
    GcdDividesA(b, r);
    var g := gcd(b, r);
    assert b % g == 0;
    assert r % g == 0;
    assert (b * q + r) % g == 0;
    assert a % g == 0;
    assert gcd(a, b) == g;
  }
}

lemma LcmPositive(a: int, b: int)
  requires a > 0 && b > 0
  ensures (a * b) / gcd(a, b) > 0
{
  GcdDividesA(a, b);
  var g := gcd(a, b);
  assert g > 0;
  assert a % g == 0;
  var k := a / g;
  assert a == g * k;
  assert k >= 1;
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
  /* code modified by LLM (iteration 3): prove lcm > 0 before division */
  LcmPositive(a, b);
  var g := gcd(a, b);
  GcdDividesA(a, b);
  var k := a / g;
  assert a == g * k;
  assert k >= 1;
  var lcm := (a * b) / g;
  assert lcm == k * b;
  assert lcm >= 1;
  var full_cycles := n / lcm;
  var remainder := n % lcm;
  var cost_a := p;
  var cost_b := q;
  var base_cost := full_cycles * (cost_a + cost_b);
  var extra_cost := 0;
  if remainder >= a && remainder >= b {
    extra_cost := cost_a + cost_b;
  } else if remainder >= a {
    extra_cost := cost_a;
  } else if remainder >= b {
    extra_cost := cost_b;
  }
  result := base_cost + extra_cost;
}
// </vc-code>
