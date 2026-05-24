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
/* helper modified by LLM (iteration 5): simplified correct lemmas */
lemma GcdSymmetric(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) == gcd(b, a)
  decreases a + b
{
  if a == b {
    assert gcd(a, b) == a;
    assert gcd(b, a) == b;
  } else if a > b {
    calc {
      gcd(a, b);
      == gcd(b, a % b);
    }
    calc {
      gcd(b, a);
      == gcd(a, b % a);
    }
    GcdSymmetric(b, a % b);
  } else {
    GcdSymmetric(b, a);
  }
}

lemma GcdLeA(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) <= a
  decreases b
{
  if a % b == 0 {
    assert gcd(a, b) == gcd(b, a % b);
    assert a % b == 0;
    assert gcd(a, b) == b;
    assert b <= a || b > a;
    if b > a {
      assert a % b == a;
      assert a == 0;
      assert false;
    }
  } else {
    assert gcd(a, b) == gcd(b, a % b);
    GcdLeA(b, a % b);
    assert gcd(b, a % b) <= b;
    assert gcd(a, b) <= b;
    if b > a {
      GcdSymmetric(a, b);
      GcdLeA(b, a);
    }
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
  /* code modified by LLM (iteration 5): simple and direct */
  var g := gcd(a, b);
  GcdLeA(a, b);
  assert g <= a;
  var lcm := (a * b) / g;
  var countA := n / a;
  var countB := n / b;
  var countLcm := n / lcm;
  var bonus := if p >= q then p else q;
  var total := countA * p + countB * q - countLcm * bonus;
  if total < 0 {
    result := 0;
  } else {
    result := total;
  }
}
// </vc-code>
