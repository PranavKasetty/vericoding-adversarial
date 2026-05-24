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
/* helper modified by LLM (iteration 3): lemmas to prove gcd divides a and lcm is positive */
lemma GcdDividesA(a: int, b: int)
  requires a > 0 && b >= 0
  ensures a % gcd(a, b) == 0
  decreases b
{
  if b == 0 {
    assert gcd(a, b) == a;
  } else {
    GcdDividesA(b, a % b);
    var g := gcd(a, b);
    assert g == gcd(b, a % b);
    assert b % g == 0;
    assert (a % b) % g == 0;
    assert a % g == (a / b * b + a % b) % g;
    assert (a / b * b) % g == 0;
  }
}

lemma DivAtLeastOne(a: int, g: int)
  requires a > 0 && g > 0 && a % g == 0
  ensures a / g >= 1
{
  assert a >= g;
}

lemma LcmPositive(a: int, b: int)
  requires a > 0 && b > 0
  ensures a / gcd(a, b) * b > 0
{
  var g := gcd(a, b);
  GcdDividesA(a, b);
  DivAtLeastOne(a, g);
  assert a / g >= 1;
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
  /* code modified by LLM (iteration 3): use lemmas to prove lcm_ab > 0 */
  var g := gcd(a, b);
  GcdDividesA(a, b);
  DivAtLeastOne(a, g);
  LcmPositive(a, b);
  var lcm_ab := a / g * b;
  assert lcm_ab > 0;
  var count_a := n / a;
  var count_b := n / b;
  var count_ab := n / lcm_ab;
  var bonus := if p < q then q else p;
  var total := count_a * p + count_b * q - count_ab * bonus;
  if total < 0 {
    result := 0;
  } else {
    result := total;
  }
}
// </vc-code>
