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
{
  var p := power(10, k);
  // We need the smallest positive multiple of n that is also a multiple of p.
  // That is lcm(n, p).
  // lcm(n, p) = n * p / gcd(n, p)
  var g := gcd(n, p);
  result := n / g * p;

  // Prove result > 0
  assert n > 0;
  assert p > 0;
  assert g > 0;
  assert n / g >= 1;
  assert result == n / g * p;

  // Prove result % n == 0
  assert (n / g * p) % n == 0 by {
    var q := n / g;
    var r := n % g;
    gcd_divides_lemma(n, p);
    assert g != 0;
    assert n % g == 0;
    assert n == q * g;
    assert result == q * p;
    assert result % n == (q * p) % (q * g);
    mod_mul_lemma(q, p, g);
  }

  // Prove result % p == 0
  assert result % p == 0 by {
    gcd_divides_lemma(n, p);
    assert p % g == 0;
    var qp := p / g;
    assert p == qp * g;
    assert result == n / g * p;
    // result = (n/g) * p, so p divides result
    mul_mod_lemma(n / g, p);
  }

  // Prove minimality
  forall_min_proof(n, p, g, result);
}
// </vc-code>
