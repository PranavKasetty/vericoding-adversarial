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
  assert lcm(a, b) == a / gcd(a, b) * b;
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
  var l := a / g * b;
  lcm_pos(a, b);
  // Count multiples of a up to n
  var countA := n / a;
  // Count multiples of b up to n
  var countB := n / b;
  // Count multiples of lcm(a,b) up to n (inclusion-exclusion)
  var countLCM := n / l;
  // Total count by inclusion-exclusion
  var count := countA + countB - countLCM;
  // Each multiple of a contributes p, each multiple of b contributes q
  // But need non-negative result
  var total := countA * p + countB * q - countLCM * (p + q);
  if total < 0 {
    result := 0;
  } else {
    result := total;
  }
}
// </vc-code>
