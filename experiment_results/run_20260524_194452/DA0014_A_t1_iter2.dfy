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

/* helper modified by LLM (iteration 2): prove gcd divides both arguments */
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

/* helper modified by LLM (iteration 2): gcd scales linearly */
lemma GcdScale(a: int, b: int, g: int)
  requires a >= 0 && b > 0 && g > 0
  ensures gcd(a * g, b * g) == g * gcd(a, b)
  decreases a + b
{
  if a == 0 {
  } else if a <= b {
    calc {
      gcd(a * g, b * g);
      == gcd(a * g, b * g - a * g);
      == { assert b * g - a * g == (b - a) * g; }
         gcd(a * g, (b - a) * g);
      == { GcdScale(a, b - a, g); }
         g * gcd(a, b - a);
      == g * gcd(a, b);
    }
  } else {
    calc {
      gcd(a * g, b * g);
      == gcd(a * g - b * g, b * g);
      == { assert a * g - b * g == (a - b) * g; }
         gcd((a - b) * g, b * g);
      == { GcdScale(a - b, b, g); }
         g * gcd(a - b, b);
      == g * gcd(a, b);
    }
  }
}

/* helper modified by LLM (iteration 2): gcd of a/g and b/g is 1 when g = gcd(a,b) */
lemma GcdOfReduced(a: int, b: int)
  requires a >= 0 && b > 0
  ensures var g := gcd(a, b); g >= 1 && gcd(a / g, b / g) == 1
{
  var g := gcd(a, b);
  GcdDivides(a, b);
  var a' := a / g;
  var b' := b / g;
  assert a == a' * g;
  assert b == b' * g;
  GcdScale(a', b', g);
  assert gcd(a' * g, b' * g) == g * gcd(a', b');
  assert gcd(a, b) == g * gcd(a', b');
  assert g == g * gcd(a', b');
  assert gcd(a', b') == 1;
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
  /* code modified by LLM (iteration 2): compute reduced fraction w/(w+b) */
  var g := gcd(w, w + b);
  GcdDivides(w, w + b);
  numerator := w / g;
  denominator := (w + b) / g;
  GcdOfReduced(w, w + b);
}
// </vc-code>
