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
/* helper modified by LLM (iteration 2): simplified helpers with direct proofs */
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

lemma gcd_divides_both(a: int, b: int)
    requires a > 0 && b >= 0
    ensures a % gcd(a, b) == 0
    ensures b % gcd(a, b) == 0
    decreases b
{
    if b == 0 {} else {
        gcd_divides_both(b, a % b);
        var g := gcd(b, a % b);
        assert b % g == 0;
        assert (a % b) % g == 0;
        assert a == (a / b) * b + (a % b);
        assert a % g == ((a / b) * b + (a % b)) % g;
        assert ((a / b) * b) % g == 0;
        assert a % g == 0;
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
    gcd_divides_both(a, b);
    var g := gcd(a, b);
    var ag := a / g;
    assert a == g * ag;
    assert ag >= 1;
    assert a * b / g == ag * b;
    assert ag * b >= 1;
}

lemma lcm_multiples(a: int, b: int)
    requires a > 0 && b > 0
    ensures lcm(a, b) % a == 0
    ensures lcm(a, b) % b == 0
{
    gcd_positive(a, b);
    gcd_divides_both(a, b);
    var g := gcd(a, b);
    var ag := a / g;
    var bg := b / g;
    assert a == g * ag;
    assert b == g * bg;
    var l := a * b / g;
    assert l == ag * b;
    assert l == a * bg;
    assert l % a == 0;
    assert l % b == 0;
}

lemma lcm_is_minimum(a: int, b: int, c: int)
    requires a > 0 && b > 0 && c > 0
    requires c % a == 0 && c % b == 0
    ensures lcm(a, b) <= c
{
    gcd_positive(a, b);
    gcd_divides_both(a, b);
    var g := gcd(a, b);
    var ag := a / g;
    var bg := b / g;
    assert a == g * ag;
    assert b == g * bg;
    var l := a * b / g;
    assert l == a * bg;
    assert l == b * ag;
    var qa := c / a;
    assert c == qa * a;
    var qb := c / b;
    assert c == qb * b;
    assert qa * ag == qb * bg;
    assert (qa * ag) % bg == 0;
    assert qa % bg == 0 || ag % bg == 0;
    calc {
        c * g;
        == qa * a * g;
        == qa * g * ag * g;
    }
    assert c * g == qa * a * g;
    assert c * g % (a * b) == 0 by {
        assert c == qa * a;
        assert c == qb * b;
        assert qa * a * g == qa * g * ag * g;
        assert a * b == g * ag * g * bg;
        assert qa * ag == qb * bg;
        var t := qb;
        assert c == t * b;
        assert c == t * g * bg;
        assert c % (g * bg) == 0;
        assert l == a * bg;
        assert c % l == 0 by {
            assert c == qa * a;
            assert qa * ag == qb * bg;
            assert bg > 0;
            var r := qa % bg;
            assert (qa * ag) % bg == 0;
            assert (r * ag) % bg == 0;
            assert qa == (qa / bg) * bg + r;
            assert c == qa * a == ((qa/bg)*bg + r) * a;
            assert c == (qa/bg) * bg * a + r * a;
            assert c == (qa/bg) * l + r * a;
            assert c % l == (r * a) % l;
            assert r * a < bg * a;
            assert r * a < l;
            assert r * a >= 0;
            assert c % l == r * a;
            assert r * ag % bg == 0;
            assert r == 0 by {
                if r > 0 {
                    assert r * ag % bg == 0;
                    assert r < bg;
                    assert ag % bg == 0 || r == 0;
                    assert false;
                }
            }
            assert c % l == 0;
        }
        assert c * g % (a * b) == 0;
    }
    assert c % l == 0;
    assert c >= l;
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
/* code modified by LLM (iteration 2): compute lcm(n, power(10,k)) */
{
    var p10k := power(10, k);
    if p10k <= 0 {
        result := n;
    } else {
        var ans := lcm(n, p10k);
        lcm_positive(n, p10k);
        lcm_multiples(n, p10k);
        forall m | m > 0 && m % n == 0 && m % p10k == 0
            ensures ans <= m
        {
            lcm_is_minimum(n, p10k, m);
        }
        result := ans;
    }
}
// </vc-code>
