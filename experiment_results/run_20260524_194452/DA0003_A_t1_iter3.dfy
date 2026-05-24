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
/* helper modified by LLM (iteration 3): add lemma proving gcd divides a and gcd <= a */
lemma GcdDividesA(a: int, b: int)
  requires a > 0 && b >= 0
  ensures gcd(a, b) <= a
  decreases b
{
  if b == 0 {
    // gcd(a, 0) = a
  } else {
    GcdDividesA(b, a % b);
    // gcd(a, b) = gcd(b, a % b) <= b <= a is not always true
    // but gcd(b, a%b) divides b, so gcd(b, a%b) <= b
    // and gcd(a,b) = gcd(b, a%b)
    // We need gcd(a,b) <= a
    // gcd(a,b) divides a, so gcd(a,b) <= a
    GcdDividesFirst(a, b);
  }
}

lemma GcdDividesFirst(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) <= a
  decreases b
{
  if b == 0 {
  } else {
    var g := gcd(a, b);
    // gcd(a,b) = gcd(b, a%b)
    // By induction gcd(b, a%b) <= b
    if a % b == 0 {
      // gcd(b, 0) = b, gcd(a,b) = b
      // b divides a, b <= a
      assert gcd(a, b) == b;
      assert b <= a by {
        // b divides a and a > 0 so b <= a
        assert a % b == 0;
        assert a / b >= 1 by { assert a >= b; }
      }
    } else {
      GcdDividesFirst(b, a % b);
      assert gcd(b, a % b) <= b;
      assert gcd(a, b) == gcd(b, a % b);
      assert gcd(a, b) <= b;
      assert b <= a || b < a;
      if b <= a {
        assert gcd(a, b) <= a;
      }
    }
  }
}

lemma LcmPositive(a: int, b: int)
  requires a > 0 && b > 0
  ensures (a * b) / gcd(a, b) >= 1
{
  assert gcd(a, b) > 0;
  assert gcd(a, b) <= a by {
    GcdDivLemma(a, b);
  }
  assert a * b >= a;
  assert a >= gcd(a, b);
  assert a * b >= gcd(a, b);
  assert (a * b) / gcd(a, b) >= 1 by {
    assert a * b >= gcd(a, b) > 0;
  }
}

lemma GcdDivLemma(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) <= a
  decreases b
{
  if a % b == 0 {
    assert gcd(a, b) == b;
    assert b <= a;
  } else {
    GcdDivLemma(b, a % b);
    assert gcd(b, a % b) <= b;
    assert gcd(a, b) == gcd(b, a % b);
    assert gcd(a, b) <= b;
    assert b < a || b == a;
    if b == a { assert a % b == 0; assert false; }
    assert b < a;
    assert gcd(a, b) <= a;
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
  /* code modified by LLM (iteration 3): use LcmPositive lemma */
  LcmPositive(a, b);
  var g := gcd(a, b);
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
