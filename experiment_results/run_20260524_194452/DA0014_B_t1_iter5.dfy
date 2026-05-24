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
/* helper modified by LLM (iteration 5): simplified GcdDivides with cleaner arithmetic and removed unused ModAdd */
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

lemma GcdDivides(a: int, b: int)
  requires a >= 0 && b > 0
  ensures gcd(a, b) > 0
  ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
  decreases a + b
{
  GcdPos(a, b);
  if a == 0 {
    assert gcd(0, b) == b;
    assert 0 % b == 0;
    assert b % b == 0;
  } else if a < b {
    GcdDivides(a, b - a);
    var g := gcd(a, b);
    assert g == gcd(a, b - a);
    assert a % g == 0;
    assert (b - a) % g == 0;
    assert b % g == (a + (b - a)) % g;
    var qa := a / g;
    var qba := (b - a) / g;
    assert a == qa * g;
    assert b - a == qba * g;
    assert b == qa * g + qba * g;
    assert b == (qa + qba) * g;
    assert b % g == 0;
  } else {
    GcdDivides(a - b, b);
    var g := gcd(a, b);
    assert g == gcd(a - b, b);
    assert (a - b) % g == 0;
    assert b % g == 0;
    var qab := (a - b) / g;
    var qb := b / g;
    assert a - b == qab * g;
    assert b == qb * g;
    assert a == qab * g + qb * g;
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

lemma GcdOne(a: int, b: int, g: int)
  requires a >= 0 && b > 0 && g > 0
  requires a % g == 0 && b % g == 0
  requires gcd(a, b) == g
  ensures gcd(a / g, b / g) == 1
{
  var p := a / g;
  var q := b / g;
  assert a == p * g;
  assert b == q * g;
  assert p >= 0 && q > 0;
  GcdScaling(p, q, g);
  assert gcd(p * g, q * g) == gcd(p, q) * g;
  assert gcd(a, b) == gcd(p, q) * g;
  assert g == gcd(p, q) * g;
  assert gcd(p, q) == 1;
}
// </vc-helpers>

// <vc-spec>
method solve(t: int, w: int, b: int) returns (numerator: int, denominator: int)
  requires ValidInput(t, w, b)
  ensures ValidFraction(numerator, denominator)
  ensures IsIrreducibleFraction(numerator, denominator)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute w/(w+b) reduced by gcd using GcdOne lemma */
{
  var num := w;
  var den := w + b;
  GcdDivides(num, den);
  var g := gcd(num, den);
  numerator := num / g;
  denominator := den / g;
  GcdOne(num, den, g);
}
// </vc-code>
