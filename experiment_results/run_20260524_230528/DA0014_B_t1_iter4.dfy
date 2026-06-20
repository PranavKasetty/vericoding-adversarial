// <vc-preamble>
predicate ValidInput(t: int, w: int, b: int)
{
  t > 0 && w > 0 && b > 0
}

predicate ValidFraction(numerator: int, denominator: int)
{
  numerator >= 0 && denominator > 0 && numerator <= denominator
}

predicate IsIrreducibleFraction(numerator: int, denominator: int)
  requires ValidFraction(numerator, denominator)
{
  gcd(numerator, denominator) == 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): use modulo-based GCD for faster verification */
function gcd(a: int, b: int): int
  requires a >= 0 && b > 0
  decreases a
{
  if a == 0 then b
  else gcd(b % a, a)
}

lemma GcdDividesNumerator(a: int, b: int)
  requires a >= 0 && b > 0
  ensures gcd(a, b) > 0
  ensures a % gcd(a, b) == 0
  decreases a
{
  if a == 0 {
  } else {
    GcdDividesNumerator(b % a, a);
    GcdDividesDenominator(b % a, a);
    var g := gcd(b % a, a);
    assert g == gcd(a, b);
    assert a % g == 0;
    assert (b % a) % g == 0;
    var q := a / g;
    var r := b % a;
    assert a == q * g;
    assert r % g == 0;
    var p := r / g;
    assert r == p * g;
    assert b % a == r;
    var d := b / a;
    assert b == d * a + r;
    assert b == d * q * g + p * g;
    assert b == (d * q + p) * g;
    assert a % g == 0;
  }
}

lemma GcdDividesDenominator(a: int, b: int)
  requires a >= 0 && b > 0
  ensures gcd(a, b) > 0
  ensures b % gcd(a, b) == 0
  decreases a
{
  if a == 0 {
  } else {
    GcdDividesDenominator(b % a, a);
    var g := gcd(b % a, a);
    assert g == gcd(a, b);
    assert a % g == 0;
    GcdDividesNumerator(b % a, a);
    assert (b % a) % g == 0;
    var q := b / a;
    var r := b % a;
    assert b == q * a + r;
    var qa := a / g;
    var qr := r / g;
    assert a == qa * g;
    assert r == qr * g;
    assert b == q * qa * g + qr * g;
    assert b == (q * qa + qr) * g;
  }
}

lemma GcdScaling(a: int, b: int, g: int)
  requires a >= 0 && b > 0 && g > 0
  ensures gcd(a * g, b * g) == g * gcd(a, b)
  decreases a
{
  if a == 0 {
  } else {
    var r := b % a;
    assert (b * g) % (a * g) == r * g by {
      var q := b / a;
      assert b == q * a + r;
      assert b * g == q * (a * g) + r * g;
    }
    GcdScaling(r, a, g);
    assert gcd(r * g, a * g) == g * gcd(r, a);
    assert gcd(a * g, b * g) == gcd((b * g) % (a * g), a * g);
    assert (b * g) % (a * g) == r * g;
    assert gcd(a * g, b * g) == gcd(r * g, a * g);
    assert gcd(r * g, a * g) == g * gcd(r, a);
    assert gcd(r, a) == gcd(b % a, a);
    assert gcd(a, b) == gcd(b % a, a);
  }
}

lemma GcdOfDivided(a: int, b: int)
  requires a >= 0 && b > 0
  ensures var g := gcd(a, b); g > 0 && a % g == 0 && b % g == 0 && gcd(a / g, b / g) == 1
  decreases a
{
  GcdDividesNumerator(a, b);
  GcdDividesDenominator(a, b);
  var g := gcd(a, b);
  var a2 := a / g;
  var b2 := b / g;
  assert a == a2 * g;
  assert b == b2 * g;
  GcdScaling(a2, b2, g);
  assert gcd(a2 * g, b2 * g) == g * gcd(a2, b2);
  assert gcd(a, b) == g * gcd(a2, b2);
  assert g == g * gcd(a2, b2);
  assert gcd(a2, b2) == 1;
}
// </vc-helpers>

// <vc-spec>
method solve(t: int, w: int, b: int) returns (numerator: int, denominator: int)
  requires ValidInput(t, w, b)
  ensures ValidFraction(numerator, denominator)
  ensures IsIrreducibleFraction(numerator, denominator)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): compute w/(w+b) in lowest terms */
  var num := w;
  var den := w + b;
  GcdOfDivided(num, den);
  var g := gcd(num, den);
  numerator := num / g;
  denominator := den / g;
}
// </vc-code>
