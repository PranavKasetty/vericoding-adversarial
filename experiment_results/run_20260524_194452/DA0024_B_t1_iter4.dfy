// <vc-preamble>
function power(base: int, exp: int): int
    requires exp >= 0
    ensures exp == 0 ==> power(base, exp) == 1
    ensures base > 0 ==> power(base, exp) > 0
    ensures base != 0 ==> power(base, exp) != 0
    decreases exp
{
    if exp == 0 then 1
    else base * power(base, exp - 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): simplified gcd without universal quantifier to avoid timeout, plus lcm divides lemmas */
function gcd(a: int, b: int): int
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
  decreases a + b
{
  if a == b then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}

lemma gcd_max(a: int, b: int, d: int)
  requires a > 0 && b > 0 && d > 0
  requires a % d == 0 && b % d == 0
  ensures d <= gcd(a, b)
  decreases a + b
{
  if a == b {
  } else if a > b {
    assert (a - b) % d == 0;
    gcd_max(a - b, b, d);
  } else {
    assert (b - a) % d == 0;
    gcd_max(a, b - a, d);
  }
}

lemma lcm_divides_common(a: int, b: int, m: int)
  requires a > 0 && b > 0 && m > 0
  requires m % a == 0 && m % b == 0
  ensures m % (a / gcd(a, b) * b) == 0
  decreases a + b
{
  var g := gcd(a, b);
  gcd_max(a, b, g);
  var qa := a / g;
  var qb := b / g;
  assert a == qa * g;
  assert b == qb * g;
  var lcm := qa * b;
  assert lcm == qa * qb * g;
  var qma := m / a;
  assert m == qma * a;
  assert m == qma * qa * g;
  var qmb := m / b;
  assert m == qmb * b;
  assert m == qmb * qb * g;
  // qma * qa == qmb * qb
  assert qma * qa * g == qmb * qb * g;
  assert g > 0;
  assert qma * qa == qmb * qb;
  // m / lcm = qmb
  assert m == qmb * lcm by {
    calc {
      qmb * lcm;
      == qmb * (qa * b);
      == qmb * qa * b;
      == qmb * qa * qb * g;
      == qma * qa * qb * g;
      == qma * (qa * g);
      == qma * a;
      == m;
    }
  }
  assert m % lcm == 0;
}

// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires n > 0 && k >= 0
    ensures result > 0
    ensures result % n == 0
    ensures result % power(10, k) == 0
    ensures forall m :: m > 0 && m % n == 0 && m % power(10, k) == 0 ==> result <= m
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): compute lcm(n, power(10,k)) with helper lemmas for minimality */
{
  var p := power(10, k);
  var g := gcd(n, p);
  result := n / g * p;
  var qa := n / g;
  var qb := p / g;
  assert n == qa * g;
  assert p == qb * g;
  assert result == qa * p;
  assert result == qa * qb * g;
  assert result > 0 by {
    assert qa >= 1;
    assert p > 0;
  }
  assert result % n == 0 by {
    assert result == qb * n by {
      calc {
        qb * n;
        == qb * (qa * g);
        == qa * qb * g;
        == result;
      }
    }
  }
  assert result % p == 0 by {
    assert result == qa * p;
  }
  forall m | m > 0 && m % n == 0 && m % p == 0
    ensures result <= m
  {
    lcm_divides_common(n, p, m);
    assert m % result == 0;
    assert m >= result by {
      assert result > 0;
      assert m > 0;
      var q := m / result;
      assert m == q * result;
      assert q >= 1;
    }
  }
}
// </vc-code>
