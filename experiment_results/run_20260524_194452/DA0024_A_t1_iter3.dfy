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
/* helper modified by LLM (iteration 3): simplified helpers to avoid timeouts and division by zero */
function gcd(a: int, b: int): int
    requires a > 0 && b >= 0
    decreases b
{
    if b == 0 then a
    else gcd(b, a % b)
}

lemma gcd_positive(a: int, b: int)
    requires a > 0 && b >= 0
    ensures gcd(a, b) > 0
    decreases b
{
    if b == 0 {} else { gcd_positive(b, a % b); }
}

lemma gcd_divides_a(a: int, b: int)
    requires a > 0 && b >= 0
    ensures gcd_positive(a, b); a % gcd(a, b) == 0
    decreases b
{
    gcd_positive(a, b);
    if b == 0 {
        assert gcd(a, 0) == a;
        assert a % a == 0;
    } else {
        gcd_divides_a(b, a % b);
        gcd_divides_b(b, a % b);
        var g := gcd(a, b);
        gcd_positive(a, b);
        assert g == gcd(b, a % b);
        assert b % g == 0;
        assert (a % b) % g == 0;
        assert a == (a / b) * b + (a % b);
        var q := a / b;
        assert a % g == ((q * b) + (a % b)) % g == 0;
    }
}

lemma gcd_divides_b(a: int, b: int)
    requires a > 0 && b >= 0
    ensures gcd_positive(a, b); b % gcd(a, b) == 0
    decreases b
{
    gcd_positive(a, b);
    if b == 0 {
        assert gcd(a, 0) == a;
        assert 0 % a == 0;
    } else {
        gcd_divides_a(b, a % b);
        var g := gcd(a, b);
        assert g == gcd(b, a % b);
        assert b % g == 0;
    }
}

function lcm(a: int, b: int): int
    requires a > 0 && b > 0
{
    gcd_positive(a, b);
    a * b / gcd(a, b)
}

lemma lcm_positive(a: int, b: int)
    requires a > 0 && b > 0
    ensures lcm(a, b) > 0
{
    gcd_positive(a, b);
    gcd_divides_a(a, b);
    var g := gcd(a, b);
    assert a % g == 0;
    var ag := a / g;
    assert a == g * ag && ag >= 1;
    assert a * b / g == ag * b;
    assert ag * b >= b >= 1;
}

lemma lcm_multiples(a: int, b: int)
    requires a > 0 && b > 0
    ensures lcm(a, b) % a == 0
    ensures lcm(a, b) % b == 0
{
    gcd_positive(a, b);
    gcd_divides_a(a, b);
    gcd_divides_b(a, b);
    var g := gcd(a, b);
    var ag := a / g;
    var bg := b / g;
    assert a == g * ag;
    assert b == g * bg;
    assert a * b / g == ag * b;
    assert ag * b % a == 0;
    assert a * b / g == a * bg;
    assert a * bg % b == 0;
}

lemma lcm_is_minimum(a: int, b: int, c: int)
    requires a > 0 && b > 0 && c > 0
    requires c % a == 0 && c % b == 0
    ensures lcm(a, b) <= c
{
    gcd_positive(a, b);
    gcd_divides_a(a, b);
    gcd_divides_b(a, b);
    var g := gcd(a, b);
    var bg := b / g;
    assert b == g * bg;
    var l := a * b / g;
    assert l == a * bg;
    var qa := c / a;
    assert c == qa * a;
    assert (qa * a) % b == 0;
    assert (qa * a) % (g * bg) == 0;
    assert a % g == 0;
    var ag := a / g;
    assert a == g * ag;
    assert qa * g * ag % (g * bg) == 0;
    assert qa * ag % bg == 0;
    assert qa % bg == 0 || ag % bg == 0;
    var r := qa % bg;
    assert r * ag % bg == 0;
    if r != 0 {
        assert r >= 1 && r < bg;
        assert ag % bg == 0;
        assert ag >= bg;
        assert ag >= 1;
    }
    assert r == 0 || ag >= bg;
    if r == 0 {
        assert qa >= bg;
        assert c == qa * a >= bg * a == l;
    } else {
        assert ag >= bg;
        assert ag * g == a >= bg * g;
        assert l == ag * b == ag * g * bg;
        assert c == qa * a == qa * ag * g;
        assert c >= 1 * ag * g >= bg * g;
        assert qa >= 1;
        assert c >= ag * g * bg == l;
    }
}
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
/* code modified by LLM (iteration 3): compute lcm(n, power(10,k)) */
{
    var p10k := power(10, k);
    if p10k <= 0 {
        result := n;
    } else {
        lcm_positive(n, p10k);
        lcm_multiples(n, p10k);
        var ans := lcm(n, p10k);
        forall m | m > 0 && m % n == 0 && m % p10k == 0
            ensures ans <= m
        {
            lcm_is_minimum(n, p10k, m);
        }
        result := ans;
    }
}
// </vc-code>
