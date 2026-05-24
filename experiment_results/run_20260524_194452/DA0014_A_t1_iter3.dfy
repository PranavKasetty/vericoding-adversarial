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

/* helper modified by LLM (iteration 3): prove gcd divides both arguments */
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
    var g := gcd(a, b - a);
    assert gcd(a, b) == g;
    assert a % g == 0;
    assert (b - a) % g == 0;
    assert b % g == 0;
  } else {
    GcdDivides(a - b, b);
    var g := gcd(a - b, b);
    assert gcd(a, b) == g;
    assert (a - b) % g == 0;
    assert b % g == 0;
    assert a % g == 0;
  }
}

/* helper modified by LLM (iteration 3): gcd of reduced fraction is 1 */
lemma GcdOfReduced(a: int, b: int)
  requires a >= 0 && b > 0
  ensures var g := gcd(a, b); g >= 1 && a % g == 0 && b % g == 0 && gcd(a / g, b / g) == 1
{
  GcdDivides(a, b);
  var g := gcd(a, b);
  var a' := a / g;
  var b' := b / g;
  assert a == a' * g;
  assert b == b' * g;
  GcdScaleInverse(a', b', g);
}

/* helper modified by LLM (iteration 3): if gcd(a*g, b*g) == g then gcd(a,b) == 1 */
lemma GcdScaleInverse(a: int, b: int, g: int)
  requires a >= 0 && b > 0 && g > 0
  ensures gcd(a * g, b * g) == g * gcd(a, b)
  decreases a + b
{
  if a == 0 {
    assert a * g == 0;
    assert b * g > 0;
    assert gcd(0, b * g) == b * g;
    assert gcd(0, b) == b;
  } else if a <= b {
    assert a * g <= b * g;
    GcdScaleInverse(a, b - a, g);
    assert gcd(a * g, (b - a) * g) == g * gcd(a, b - a);
    assert (b - a) * g == b * g - a * g;
    assert gcd(a * g, b * g) == gcd(a * g, b * g - a * g);
    assert gcd(a * g, b * g) == g * gcd(a, b - a);
    assert gcd(a, b) == gcd(a, b - a);
  } else {
    assert a * g > b * g;
    GcdScaleInverse(a - b, b, g);
    assert gcd((a - b) * g, b * g) == g * gcd(a - b, b);
    assert (a - b) * g == a * g - b * g;
    assert gcd(a * g, b * g) == gcd(a * g - b * g, b * g);
    assert gcd(a * g, b * g) == g * gcd(a - b, b);
    assert gcd(a, b) == gcd(a - b, b);
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
  /* code modified by LLM (iteration 3): compute reduced fraction w/(w+b) */
  var total := w + b;
  var g := gcd(w, total);
  GcdDivides(w, total);
  GcdOfReduced(w, total);
  numerator := w / g;
  denominator := total / g;
}
// </vc-code>
