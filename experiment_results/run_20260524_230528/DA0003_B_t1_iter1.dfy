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
lemma gcd_pos(a: int, b: int)
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  decreases b
{
  if b == 0 {
  } else {
    gcd_pos(b, a % b);
  }
}

function lcm(a: int, b: int): int
  requires a > 0 && b > 0
  ensures lcm(a, b) > 0
{
  a / gcd(a, b) * b
}

lemma lcm_pos(a: int, b: int)
  requires a > 0 && b > 0
  ensures lcm(a, b) > 0
{
  gcd_pos(a, b);
  assert gcd(a, b) > 0;
  assert gcd(a, b) <= a;
  assert a / gcd(a, b) >= 1;
  assert a / gcd(a, b) * b >= b;
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
  var g := gcd(a, b);
  var lcmAB := a / g * b;
  if lcmAB <= 0 {
    result := 0;
  } else {
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
}
// </vc-code>
