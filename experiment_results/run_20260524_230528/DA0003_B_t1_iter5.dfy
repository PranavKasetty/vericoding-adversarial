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
/* helper modified by LLM (iteration 5): use calc blocks and explicit decreases for termination */
lemma mul_mod_zero(q: int, b: int, g: int)
  requires g > 0 && b % g == 0
  ensures (q * b) % g == 0
  decreases if q >= 0 then q else -q
{
  if q == 0 {
    assert q * b == 0;
  } else if q > 0 {
    mul_mod_zero(q - 1, b, g);
    calc {
      q * b;
      == (q - 1) * b + b;
    }
  } else {
    mul_mod_zero(q + 1, b, g);
    calc {
      q * b;
      == (q + 1) * b - b;
    }
  }
}

lemma add_mod_zero(x: int, y: int, g: int)
  requires g > 0 && x % g == 0 && y % g == 0
  ensures (x + y) % g == 0
{
  var qx := x / g;
  var qy := y / g;
  assert x == qx * g;
  assert y == qy * g;
  assert x + y == (qx + qy) * g;
}

lemma gcd_divides(a: int, b: int)
  requires a > 0 && b >= 0
  ensures a % gcd(a, b) == 0
  decreases b
{
  if b == 0 {
  } else {
    gcd_divides(b, a % b);
    var g := gcd(a, b);
    assert g == gcd(b, a % b);
    assert b % g == 0;
    assert (a % b) % g == 0;
    var q := a / b;
    var r := a % b;
    assert a == q * b + r;
    mul_mod_zero(q, b, g);
    assert (q * b) % g == 0;
    assert r % g == 0;
    add_mod_zero(q * b, r, g);
    assert (q * b + r) % g == 0;
    assert a % g == 0;
  }
}

lemma gcd_le_a(a: int, b: int)
  requires a > 0 && b >= 0
  ensures gcd(a, b) <= a
  decreases b
{
  gcd_divides(a, b);
  var g := gcd(a, b);
  assert a % g == 0;
  assert g > 0;
  assert a >= g;
}

function lcm(a: int, b: int): int
  requires a > 0 && b > 0
  ensures lcm(a, b) > 0
{
  gcd_le_a(a, b);
  a / gcd(a, b) * b
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, p: int, q: int) returns (result: int)
  requires ValidInput(n, a, b, p, q)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): use gcd_le_a lemma to ensure lcm is positive */
  gcd_le_a(a, b);
  var g := gcd(a, b);
  var lcmAB := a / g * b;
  assert g <= a;
  assert a / g >= 1;
  assert lcmAB >= b;
  assert lcmAB > 0;
  var countA := n / a;
  var countB := n / b;
  var countLCM := n / lcmAB;
  var total := countA * p + countB * q - countLCM * (p + q);
  if total >= 0 {
    result := total;
  } else {
    result := 0;
  }
}
// </vc-code>
