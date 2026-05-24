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
/* helper modified by LLM (iteration 2): add lemma proving lcm is positive */
lemma GcdPositive(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
{
}

lemma LcmPositive(a: int, b: int)
  requires a > 0 && b > 0
  ensures a * b > 0
  ensures gcd(a, b) > 0
  ensures (a * b) / gcd(a, b) > 0
{
  GcdPositive(a, b);
  assert gcd(a, b) >= 1;
  assert a * b >= 1;
  assert (a * b) / gcd(a, b) >= 1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, p: int, q: int) returns (result: int)
  requires ValidInput(n, a, b, p, q)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): ensure lcm > 0 before dividing */
  GcdPositive(a, b);
  var g := gcd(a, b);
  assert g > 0;
  assert a * b > 0;
  LcmPositive(a, b);
  var lcm := (a * b) / g;
  assert lcm > 0;
  var countA := n / a;
  var countB := n / b;
  var countLcm := n / lcm;
  var total := countA * p + countB * q - countLcm * (if p < q then q else p);
  if total < 0 {
    result := 0;
  } else {
    result := total;
  }
}
// </vc-code>
