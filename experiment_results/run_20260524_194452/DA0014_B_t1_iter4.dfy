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
/* helper modified by LLM (iteration 4): fix ModAdd with explicit arithmetic proof and fix GcdDivides */
function gcd(a: int, b: int): int
  requires a >= 0 && b > 0
  decreases a + b
{
  if a == 0 then b
  else if a < b then gcd(a, b - a)
  else gcd(a - b, b)
}

lemma GcdPos(a: int, b: int)
  requires a >= 0 && b > 0
  ensures gcd(a, b) > 0
  decreases a + b
{
  if a == 0 {
  } else if a < b {
    GcdPos(a, b - a);
  } else {
    GcdPos(a - b, b);
  }
}

lemma ModAdd(x: int, y: int, g: int)
  requires g > 0 && x % g == 0 && y % g == 0
  ensures (x + y) % g == 0
{
  var a := x / g;
  var b := y / g;
  assert x == a * g;
  assert y == b * g;
  assert x + y == (a + b) * g;
  assert (x + y) % g == ((a + b) * g) % g;
  assert ((a + b) * g) % g == 0;
}

lemma GcdDivides(a: int, b: int)
  requires a >= 0 && b > 0
  ensures gcd(a, b) > 0
  ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
  decreases a + b
{
  GcdPos(a, b);
  if a == 0 {
  } else if a < b {
    GcdDivides(a, b - a);
    var g := gcd(a, b - a);
    assert gcd(a, b) == g;
    assert a % g == 0;
    assert (b - a) % g == 0;
    var qa := a / g;
    var qba := (b - a) / g;
    assert a == qa * g;
    assert b - a == qba * g;
    assert b == (qa + qba) * g;
    assert b % g == 0;
  } else {
    GcdDivides(a - b, b);
    var g := gcd(a - b, b);
    assert gcd(a, b) == g;
    assert (a - b) % g == 0;
    assert b % g == 0;
    var qab := (a - b) / g;
    var qb := b / g;
    assert a - b == qab * g;
    assert b == qb * g;
    assert a == (qab + qb) * g;
    assert a % g == 0;
  }
}

lemma GcdScaling(a: int, b: int, k: int)
  requires a >= 0 && b > 0 && k > 0
  ensures gcd(a * k, b * k) == gcd(a, b) * k
  decreases a + b
{
  if a == 0 {
  } else if a < b {
    calc {
      gcd(a * k, b * k);
      == gcd(a * k, b * k - a * k);
      == gcd(a * k, (b - a) * k);
      == { GcdScaling(a, b - a, k); }
         gcd(a, b - a) * k;
      == gcd(a, b) * k;
    }
  } else {
    calc {
      gcd(a * k, b * k);
      == gcd(a * k - b * k, b * k);
      == gcd((a - b) * k, b * k);
      == { GcdScaling(a - b, b, k); }
         gcd(a - b, b) * k;
      == gcd(a, b) * k;
    }
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
/* code modified by LLM (iteration 4): compute w/(w+b) reduced by gcd */
{
  var num := w;
  var den := w + b;
  GcdDivides(num, den);
  var g := gcd(num, den);
  numerator := num / g;
  denominator := den / g;
  GcdScaling(numerator, denominator, g);
  assert gcd(numerator * g, denominator * g) == gcd(numerator, denominator) * g;
  assert gcd(num, den) == gcd(numerator, denominator) * g;
  assert g == gcd(numerator, denominator) * g;
  assert gcd(numerator, denominator) == 1;
}
// </vc-code>
