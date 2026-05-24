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
/* helper modified by LLM (iteration 3): simplified gcd_divides proof to avoid timeout */
lemma gcd_divides(a: int, b: int)
  requires a > 0 && b >= 0
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
  decreases b
{
  if b == 0 {
    assert gcd(a, b) == a;
    assert a % a == 0;
    assert b % a == 0;
  } else {
    gcd_divides(b, a % b);
    var g := gcd(a, b);
    assert g == gcd(b, a % b);
    assert b % g == 0;
    assert (a % b) % g == 0;
    var k1 := b / g;
    var k2 := (a % b) / g;
    var q := a / b;
    assert a == q * b + (a % b);
    assert q * b % g == 0 by {
      assert b % g == 0;
      assert (q * b) % g == 0;
    }
    assert a % g == 0 by {
      assert a == q * b + (a % b);
      assert (q * b) % g == 0;
      assert (a % b) % g == 0;
    }
  }
}

lemma gcd_le(a: int, b: int)
  requires a > 0 && b >= 0
  ensures gcd(a, b) <= a
  decreases b
{
  if b == 0 {
  } else {
    gcd_divides(a, b);
    var g := gcd(a, b);
    assert a % g == 0;
    assert g <= a;
  }
}

lemma lcm_pos(a: int, b: int)
  requires a > 0 && b > 0
  ensures a / gcd(a, b) * b > 0
{
  gcd_divides(a, b);
  var g := gcd(a, b);
  assert g > 0;
  assert a % g == 0;
  assert a / g * g == a;
  assert a / g >= 1;
  assert a / g * b >= b;
  assert b > 0;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, p: int, q: int) returns (result: int)
  requires ValidInput(n, a, b, p, q)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): use lcm_pos lemma for proof */
  var g := gcd(a, b);
  lcm_pos(a, b);
  var l := a / g * b;
  assert l > 0;
  var countA := n / a;
  var countB := n / b;
  var countLCM := n / l;
  var total := countA * p + countB * q - countLCM * (p + q);
  if total < 0 {
    result := 0;
  } else {
    result := total;
  }
}
// </vc-code>
