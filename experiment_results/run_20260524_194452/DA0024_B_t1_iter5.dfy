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
/* helper modified by LLM (iteration 5): modulo-based gcd for faster verification */
function gcd(a: int, b: int): int
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
  decreases b
{
  if b == 0 then a
  else if a % b == 0 then b
  else gcd(b, a % b)
}

lemma gcd_max(a: int, b: int, d: int)
  requires a > 0 && b > 0 && d > 0
  requires a % d == 0 && b % d == 0
  ensures d <= gcd(a, b)
  decreases b
{
  if a % b == 0 {
    // gcd(a,b) = b, and b % d == 0 so d <= b
    assert b % d == 0;
    assert d <= b;
  } else {
    var r := a % b;
    assert r > 0;
    assert r % d == 0 by {
      var qa := a / d;
      var qb := b / d;
      assert a == qa * d;
      assert b == qb * d;
      var qr := a / b;
      assert r == a - qr * b;
      assert r == qa * d - qr * qb * d;
      assert r == (qa - qr * qb) * d;
    }
    gcd_max(b, r, d);
  }
}

lemma gcd_divides(a: int, b: int)
  requires a > 0 && b > 0
  ensures (a / gcd(a, b)) * gcd(a, b) == a
  ensures (b / gcd(a, b)) * gcd(a, b) == b
{
  var g := gcd(a, b);
  assert a % g == 0;
  assert b % g == 0;
}

lemma lcm_divides_common(a: int, b: int, m: int)
  requires a > 0 && b > 0 && m > 0
  requires m % a == 0 && m % b == 0
  ensures m % (a / gcd(a, b) * b) == 0
{
  var g := gcd(a, b);
  gcd_max(a, b, g);
  var qa := a / g;
  var qb := b / g;
  gcd_divides(a, b);
  assert a == qa * g;
  assert b == qb * g;
  var lcm := qa * b;
  assert lcm == qa * qb * g;
  var qma := m / a;
  assert m == qma * a;
  var qmb := m / b;
  assert m == qmb * b;
  assert qma * qa * g == qmb * qb * g by {
    assert qma * a == qmb * b;
    assert qma * (qa * g) == qmb * (qb * g);
  }
  assert g > 0;
  assert qma * qa == qmb * qb by {
    var lhs := qma * qa;
    var rhs := qmb * qb;
    assert lhs * g == rhs * g;
  }
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
/* code modified by LLM (iteration 5): compute lcm(n, power(10,k)) */
{
  var p := power(10, k);
  var g := gcd(n, p);
  result := n / g * p;
  var qa := n / g;
  var qb := p / g;
  gcd_divides(n, p);
  assert n == qa * g;
  assert p == qb * g;
  assert result == qa * p;
  assert result == qa * qb * g;
  assert result > 0 by {
    assert qa >= 1;
    assert qb >= 1;
    assert g > 0;
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
