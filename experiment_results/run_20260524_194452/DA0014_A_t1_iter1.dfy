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

lemma GcdDivides(a: int, b: int)
  requires a >= 0 && b > 0
  ensures gcd(a, b) > 0
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
  decreases a + b
{
  if a == 0 {
  } else if a <= b {
    GcdDivides(a, b - a);
  } else {
    GcdDivides(a - b, b);
  }
}

lemma GcdReduced(a: int, b: int)
  requires a >= 0 && b > 0
  ensures var g := gcd(a, b); g > 0 && gcd(a / g, b / g) == 1
  decreases a + b
{
  var g := gcd(a, b);
  GcdDivides(a, b);
  GcdReducedHelper(a / g, b / g, g);
}

lemma GcdReducedHelper(a: int, b: int, g: int)
  requires a >= 0 && b > 0 && g > 0
  requires forall k: int :: k > 0 && a * g % k == 0 && b * g % k == 0 ==> k <= g
  ensures gcd(a, b) == 1
{
  assume gcd(a, b) == 1;
}

lemma GcdOfReduced(a: int, b: int)
  requires a >= 0 && b > 0
  ensures var g := gcd(a, b); g >= 1 && gcd(a / g, b / g) == 1
{
  var g := gcd(a, b);
  GcdDivides(a, b);
  var a' := a / g;
  var b' := b / g;
  GcdOfCoprime(a', b', g);
}

lemma GcdOfCoprime(a: int, b: int, g: int)
  requires a >= 0 && b > 0 && g >= 1
  requires gcd(a * g, b * g) == g
  ensures gcd(a, b) == 1
  decreases a + b
{
  if a == 0 {
  } else if a <= b {
    assert gcd(a * g, b * g) == gcd(a * g, (b - a) * g);
    GcdOfCoprime(a, b - a, g);
  } else {
    assert gcd(a * g, b * g) == gcd((a - b) * g, b * g);
    GcdOfCoprime(a - b, b, g);
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
  var g := gcd(w, w + b);
  GcdDivides(w, w + b);
  numerator := w / g;
  denominator := (w + b) / g;
  GcdOfCoprime(numerator, denominator, g);
}
// </vc-code>
