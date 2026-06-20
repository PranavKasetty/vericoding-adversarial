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
function gcd(a: int, b: int): int
  requires a >= 0 && b > 0
  decreases a + b
{
  if a == 0 then b
  else if a <= b then gcd(a, b - a)
  else gcd(a - b, b)
}

lemma GcdDividesNumerator(a: int, b: int)
  requires a >= 0 && b > 0
  ensures gcd(a, b) > 0
  ensures a % gcd(a, b) == 0
  decreases a + b
{
  if a == 0 { }
  else if a <= b {
    GcdDividesNumerator(a, b - a);
    var g := gcd(a, b - a);
    assert g == gcd(a, b);
  } else {
    GcdDividesNumerator(a - b, b);
    var g := gcd(a - b, b);
    assert g == gcd(a, b);
  }
}

lemma GcdDividesDenominator(a: int, b: int)
  requires a >= 0 && b > 0
  ensures gcd(a, b) > 0
  ensures b % gcd(a, b) == 0
  decreases a + b
{
  if a == 0 { }
  else if a <= b {
    GcdDividesDenominator(a, b - a);
    var g := gcd(a, b - a);
    assert g == gcd(a, b);
  } else {
    GcdDividesDenominator(a - b, b);
    var g := gcd(a - b, b);
    assert g == gcd(a, b);
  }
}

lemma GcdOfDivided(a: int, b: int)
  requires a >= 0 && b > 0
  ensures var g := gcd(a, b); g > 0 && a % g == 0 && b % g == 0 && gcd(a / g, b / g) == 1
  decreases a + b
{
  GcdDividesNumerator(a, b);
  GcdDividesDenominator(a, b);
  var g := gcd(a, b);
  GcdOfDividedHelper(a, b, g);
}

lemma GcdOfDividedHelper(a: int, b: int, g: int)
  requires a >= 0 && b > 0 && g > 0
  requires a % g == 0 && b % g == 0
  requires g == gcd(a, b)
  ensures gcd(a / g, b / g) == 1
  decreases a + b
{
  var a2 := a / g;
  var b2 := b / g;
  assert a == a2 * g;
  assert b == b2 * g;
  GcdScaling(a2, b2, g);
}

lemma GcdScaling(a: int, b: int, g: int)
  requires a >= 0 && b > 0 && g > 0
  ensures gcd(a * g, b * g) == g * gcd(a, b)
  decreases a + b
{
  if a == 0 { }
  else if a <= b {
    GcdScaling(a, b - a, g);
  } else {
    GcdScaling(a - b, b, g);
  }
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
  var num := w;
  var den := w + b;
  GcdDividesNumerator(num, den);
  GcdDividesDenominator(num, den);
  var g := gcd(num, den);
  GcdOfDivided(num, den);
  numerator := num / g;
  denominator := den / g;
}
// </vc-code>
