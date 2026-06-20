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
/* helper modified by LLM (iteration 3): fix GcdDividesNumerator else branch, fix GcdScaling */
function gcd(a: int, b: int): int
  requires a >= 0 && b > 0
  decreases a + b
{
  if a == 0 then b
  else if a == b then a
  else if a < b then gcd(a, b - a)
  else gcd(a - b, b)
}

lemma GcdDividesNumerator(a: int, b: int)
  requires a >= 0 && b > 0
  ensures gcd(a, b) > 0
  ensures a % gcd(a, b) == 0
  decreases a + b
{
  if a == 0 { }
  else if a == b { }
  else if a < b {
    GcdDividesNumerator(a, b - a);
  } else {
    GcdDividesNumerator(a - b, b);
    GcdDividesDenominator(a - b, b);
    var g := gcd(a - b, b);
    assert g == gcd(a, b);
    assert (a - b) % g == 0;
    assert b % g == 0;
  }
}

lemma GcdDividesDenominator(a: int, b: int)
  requires a >= 0 && b > 0
  ensures gcd(a, b) > 0
  ensures b % gcd(a, b) == 0
  decreases a + b
{
  if a == 0 { }
  else if a == b { }
  else if a < b {
    GcdDividesDenominator(a, b - a);
    var g := gcd(a, b - a);
    assert g == gcd(a, b);
    assert (b - a) % g == 0;
    GcdDividesNumerator(a, b - a);
    assert a % g == 0;
  } else {
    GcdDividesDenominator(a - b, b);
  }
}

lemma GcdScaling(a: int, b: int, g: int)
  requires a >= 0 && b > 0 && g > 0
  ensures gcd(a * g, b * g) == g * gcd(a, b)
  decreases a + b
{
  if a == 0 {
    assert gcd(0, b * g) == b * g;
    assert g * gcd(0, b) == g * b;
  } else if a == b {
    assert gcd(a * g, b * g) == a * g;
    assert g * gcd(a, b) == g * a;
  } else if a < b {
    calc {
      gcd(a * g, b * g);
      == gcd(a * g, b * g - a * g);
      == { assert b * g - a * g == (b - a) * g; GcdScaling(a, b - a, g); }
      g * gcd(a, b - a);
      == g * gcd(a, b);
    }
  } else {
    calc {
      gcd(a * g, b * g);
      == gcd(a * g - b * g, b * g);
      == { assert a * g - b * g == (a - b) * g; GcdScaling(a - b, b, g); }
      g * gcd(a - b, b);
      == g * gcd(a, b);
    }
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
  /* code modified by LLM (iteration 3): compute w/(w+b) in lowest terms */
  var num := w;
  var den := w + b;
  GcdOfDivided(num, den);
  var g := gcd(num, den);
  numerator := num / g;
  denominator := den / g;
}
// </vc-code>
