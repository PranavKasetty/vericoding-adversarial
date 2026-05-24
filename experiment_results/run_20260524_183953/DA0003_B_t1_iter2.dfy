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
/* helper modified by LLM (iteration 2): lemma to prove gcd divides a, enabling lcm non-zero proof */
lemma GcdDividesA(a: int, b: int)
  requires a > 0 && b >= 0
  ensures a % gcd(a, b) == 0
  decreases b
{
  if b == 0 {
    // gcd(a, 0) = a, and a % a == 0
  } else {
    // gcd(a, b) = gcd(b, a % b)
    GcdDividesA(b, a % b);
    // Now we know b % gcd(b, a%b) == 0, i.e., b % gcd(a,b) == 0
    // Also (a % b) % gcd(a,b) == 0
    // a = (a/b)*b + (a%b), so a % gcd(a,b) == 0
    var g := gcd(a, b);
    var r := a % b;
    // b % g == 0 and r % g == 0
    // a == (a / b) * b + r
    assert a == (a / b) * b + r;
    assert b % g == 0;
    assert r % g == 0;
    assert ((a / b) * b) % g == 0 by {
      var k := a / b;
      var bq := b / g;
      assert b == bq * g;
      assert k * b == k * bq * g;
    }
    assert a % g == 0 by {
      assert a == (a / b) * b + r;
      var x := (a / b) * b;
      assert x % g == 0;
      assert r % g == 0;
      assert (x + r) % g == 0;
    }
  }
}

lemma LcmPositive(a: int, b: int)
  requires a > 0 && b > 0
  ensures a / gcd(a, b) * b > 0
{
  GcdDividesA(a, b);
  var g := gcd(a, b);
  assert a % g == 0;
  assert a / g >= 1 by {
    assert g <= a;
    assert a / g >= 1;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, p: int, q: int) returns (result: int)
  requires ValidInput(n, a, b, p, q)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added LcmPositive lemma call to prove lcm_ab > 0 */
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
