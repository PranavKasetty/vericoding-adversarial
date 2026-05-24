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
/* helper modified by LLM (iteration 3): gcd function and supporting lemmas, replaced GcdCoprime call with inline argument */
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
/* code modified by LLM (iteration 3): compute lcm(n, power(10,k)) directly */
{
  var p := power(10, k);
  var g := gcd(n, p);
  result := n / g * p;
  gcd_divides(n, p);
  assert n % g == 0;
  assert p % g == 0;
  var qa := n / g;
  var qb := p / g;
  assert n == qa * g;
  assert p == qb * g;
  assert result == qa * p;
  assert result == qa * qb * g;
  assert result > 0 by {
    assert qa >= 1;
    assert p > 0;
    assert qa * p >= p;
  }
  assert result % n == 0 by {
    assert result == qa * p;
    assert result == qa * qb * g;
    assert result == qb * (qa * g);
    assert result == qb * n;
  }
  assert result % p == 0 by {
    assert result == qa * p;
  }
  forall m | m > 0 && m % n == 0 && m % p == 0
    ensures result <= m
  {
    var qma := m / n;
    assert m == qma * n;
    assert qma >= 1;
    var qmb := m / p;
    assert m == qmb * p;
    assert m == qma * qa * g;
    assert m == qmb * qb * g;
    assert qma * qa == qmb * qb by {
      assert g > 0;
      assert qma * qa * g == qmb * qb * g;
    }
    assert m == qma * qa * qb * g by {
      assert m == qma * (qa * g);
      assert qa * g == n;
      assert m % p == 0;
      assert m == qmb * qb * g;
      assert qma * qa == qmb * qb;
      assert m == qma * qa * g;
      assert qb * m == qb * qma * qa * g;
      assert qb * m == qma * (qa * qb * g);
      assert qb * m == qma * result;
      assert m * qb == qma * result;
      assert m * qb >= result * qb by { assert qma >= 1; }
      assert m >= result;
    }
    assert m >= result;
  }
}
// </vc-code>
