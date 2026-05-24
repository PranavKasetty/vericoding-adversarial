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
/* helper modified by LLM (iteration 2): gcd function and supporting lemmas */
function gcd(a: int, b: int): int
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
  ensures forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= gcd(a, b)
  decreases a + b
{
  if a == b then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}

lemma gcd_divides(a: int, b: int)
  requires a > 0 && b > 0
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
{
}

lemma mul_div_exact(a: int, b: int, g: int)
  requires a > 0 && b > 0 && g > 0
  requires a % g == 0 && b % g == 0
  ensures (a / g * b) % a == 0
  ensures (a / g * b) % b == 0
{
  var qa := a / g;
  var qb := b / g;
  assert a == qa * g;
  assert b == qb * g;
  assert a / g * b == qa * (qb * g);
  assert a / g * b == qa * qb * g;
  calc {
    (a / g * b) % a;
    == (qa * qb * g) % (qa * g);
    == { LemmaMulModMultiply(qa, qb * g, g); }
    0;
  }
  calc {
    (a / g * b) % b;
    == (qa * (qb * g)) % (qb * g);
    == { LemmaMulModMultiply(qb, qa * g, g); }
    0;
  }
}

lemma LemmaMulModMultiply(k: int, m: int, n: int)
  requires k > 0 && n > 0
  ensures (k * m) % (k * n) == k * (m % n)
{
  var q := m / n;
  var r := m % n;
  assert m == q * n + r;
  assert k * m == k * (q * n + r);
  assert k * m == k * q * n + k * r;
  assert k * m == (k * q) * (k * n) / k + k * r;
}

lemma lcm_minimal(a: int, b: int, g: int, L: int)
  requires a > 0 && b > 0 && g > 0
  requires g == gcd(a, b)
  requires L == a / g * b
  requires a % g == 0 && b % g == 0
  ensures forall m :: m > 0 && m % a == 0 && m % b == 0 ==> L <= m
{
  forall m | m > 0 && m % a == 0 && m % b == 0
    ensures L <= m
  {
    var qa := a / g;
    assert a == qa * g;
    assert L == qa * b;
    assert m % a == 0;
    var qm := m / a;
    assert m == qm * a;
    assert m == qm * qa * g;
    assert m % b == 0;
    var qmb := m / b;
    assert m == qmb * b;
    assert L <= m by {
      assert m / L * L == m || m % L != 0;
      if m < L {
        assert m > 0;
        assert m % a == 0;
        assert m % b == 0;
        assert m < a / g * b;
        LcmLowerBound(a, b, g, m);
      }
    }
  }
}

lemma LcmLowerBound(a: int, b: int, g: int, m: int)
  requires a > 0 && b > 0 && g > 0 && m > 0
  requires g == gcd(a, b)
  requires a % g == 0 && b % g == 0
  requires m % a == 0 && m % b == 0
  ensures m >= a / g * b
{
  var qa := a / g;
  var qb := b / g;
  assert a == qa * g;
  assert b == qb * g;
  var qma := m / a;
  assert m == qma * a;
  assert m == qma * qa * g;
  var qmb := m / b;
  assert m == qmb * b;
  assert m == qmb * qb * g;
  assert qma * qa == qmb * qb;
  assert m == qma * qa * g * qb;
  assert m == qma * (qa * g) * qb;
  assert m == qma * a * qb;
  assert m == qma * qb * a;
  assert m >= a by { assert qma >= 1; }
  GcdCoprime(a, b, g, qa, qb, qma, qmb);
  assert qma >= qb;
  assert m == qma * a >= qb * a;
  assert qb * a == (b / g) * a;
  assert (b / g) * a == a / g * b;
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
/* code modified by LLM (iteration 2): compute lcm(n, power(10,k)) directly */
{
  var p := power(10, k);
  var g := gcd(n, p);
  result := n / g * p;
  gcd_divides(n, p);
  assert n % g == 0;
  assert p % g == 0;
  assert result == n / g * p;
  assert result > 0 by {
    assert n / g >= 1;
    assert p > 0;
  }
  assert result % n == 0 by {
    var qa := n / g;
    assert n == qa * g;
    assert result == qa * p;
    var qb := p / g;
    assert p == qb * g;
    assert result == qa * qb * g;
    assert result == (qa * qb) * g;
    assert result / n == result / (qa * g);
    assert qa * p == qa * (qb * g);
    assert (qa * (qb * g)) % (qa * g) == 0 by {
      assert qa * (qb * g) == qb * (qa * g);
    }
  }
  assert result % p == 0 by {
    assert result == n / g * p;
    var c := n / g;
    assert result == c * p;
    assert (c * p) % p == 0;
  }
  forall m | m > 0 && m % n == 0 && m % p == 0
    ensures result <= m
  {
    assert m % n == 0;
    assert m % p == 0;
    var g2 := gcd(n, p);
    assert g2 == g;
    var qa := n / g;
    assert n == qa * g;
    var qb := p / g;
    assert p == qb * g;
    var qma := m / n;
    assert m == qma * n;
    assert m == qma * qa * g;
    var qmb := m / p;
    assert m == qmb * p;
    assert m == qmb * qb * g;
    assert qma * qa == qmb * qb by {
      assert m == qma * qa * g;
      assert m == qmb * qb * g;
      assert g > 0;
    }
    assert result == qa * p;
    assert result == qa * qb * g;
    assert m == qma * qa * qb * g by {
      assert m == qma * qa * g;
      assert qma * qa == qmb * qb;
    }
    assert m == qma * result by {
      assert result == qa * qb * g;
      assert m == qma * (qa * qb * g);
    }
    assert qma >= 1 by {
      assert m > 0;
      assert result > 0;
    }
    assert m >= result;
  }
}
// </vc-code>
