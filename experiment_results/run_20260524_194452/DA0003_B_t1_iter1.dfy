// <vc-preamble>
predicate ValidInput(n: int, a: int, b: int, p: int, q: int) {
  n > 0 && a > 0 && b > 0 && p > 0 && q > 0
}

function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}
// </vc-preamble>

// <vc-helpers>
lemma GcdPositive(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, p: int, q: int) returns (result: int)
  requires ValidInput(n, a, b, p, q)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var lcm := (a * b) / gcd(a, b);
  var full_cycles := n / lcm;
  var remainder := n % lcm;
  var cost_a := p;
  var cost_b := q;
  var base_cost := full_cycles * (cost_a + cost_b);
  var extra_cost := 0;
  if remainder >= a && remainder >= b {
    extra_cost := cost_a + cost_b;
  } else if remainder >= a {
    extra_cost := cost_a;
  } else if remainder >= b {
    extra_cost := cost_b;
  }
  result := base_cost + extra_cost;
}
// </vc-code>
