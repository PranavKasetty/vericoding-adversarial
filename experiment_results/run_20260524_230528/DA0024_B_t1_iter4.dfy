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
/* helper modified by LLM (iteration 4): simplified proofs to avoid timeouts, fixed division-by-zero */
function gcd(a: int, b: int): int
    requires a > 0 && b >= 0
    decreases b
{
    if b == 0 then a else gcd(b, a % b)
}

function lcm(a: int, b: int): int
    requires a > 0 && b > 0
    requires gcd(a, b) > 0
{
    a * b / gcd(a, b)
}

lemma GcdPos(a: int, b: int)
    requires a > 0 && b >= 0
    ensures gcd(a, b) > 0
    decreases b
{
    if b == 0 {} else { GcdPos(b, a % b); }
}

lemma GcdDividesA(a: int, b: int)
    requires a > 0 && b >= 0
    ensures gcd(a, b) > 0
    ensures a % gcd(a, b) == 0
    decreases b
{
    if b == 0 {
    } else {
        GcdDividesA(b, a % b);
        GcdDividesB(b, a % b);
        var g := gcd(b, a % b);
        var r := a % b;
        var q := a / b;
        assert a == q * b + r;
        assert b % g == 0;
        assert r % g == 0;
        ModAddLemma(q, b, r, g);
    }
}

lemma ModAddLemma(q: int, b: int, r: int, g: int)
    requires g > 0 && b % g == 0 && r % g == 0
    ensures (q * b + r) % g == 0
{
    var qb := q * b;
    assert qb % g == 0 by {
        var bq := b / g;
        assert b == bq * g;
        assert qb == q * bq * g;
    }
    var rg := r / g;
    var qbg := qb / g;
    assert qb == qbg * g;
    assert r == rg * g;
    assert q * b + r == (qbg + rg) * g;
}

lemma GcdDividesB(a: int, b: int)
    requires a > 0 && b >= 0
    ensures gcd(a, b) > 0
    ensures b % gcd(a, b) == 0
    decreases b
{
    if b == 0 {
    } else {
        GcdDividesA(b, a % b);
    }
}

lemma GcdScaleFactor(a: int, b: int, k: int)
    requires a > 0 && b >= 0 && k > 0
    ensures gcd(a * k, b * k) == gcd(a, b) * k
    decreases b
{
    if b == 0 {
    } else {
        var r := (a * k) % (b * k);
        assert r == (a % b) * k;
        GcdScaleFactor(b, a % b, k);
    }
}

lemma BezoutHelper(a: int, b: int) returns (s: int, t: int)
    requires a > 0 && b >= 0
    ensures s * a + t * b == gcd(a, b)
    decreases b
{
    if b == 0 {
        s := 1; t := 0;
    } else {
        var s1, t1 := BezoutHelper(b, a % b);
        s := t1;
        t := s1 - (a / b) * t1;
    }
}

lemma CoprimeDivides(p: int, q: int, x: int)
    requires p > 0 && q > 0 && x >= 0
    requires gcd(p, q) == 1
    requires (x * q) % p == 0
    ensures x % p == 0
{
    var s, t := BezoutHelper(p, q);
    assert s * p + t * q == 1;
    var r := x % p;
    assert x == (x / p) * p + r;
    assert (x * q) % p == (r * q) % p;
    assert (r * q) % p == 0;
    if r != 0 {
        assert r > 0 && r < p;
        assert (r * q) % p == 0;
        assert r * (s * p + t * q) == r;
        assert (r * s * p + r * t * q) == r;
        assert (r * t * q) % p == r % p;
        assert (r * t * q) % p == r;
        assert (r * q) % p == 0;
        assert (r * t * (r * q)) % p == 0;
        var rq := r * q;
        assert rq % p == 0;
        assert r == r * s * p + r * t * q;
        assert r % p == (r * t * q) % p;
        assert r % p == (r * t) % p * (q % p) % p;
        assert r == r * 1;
        assert r == r * (s * p + t * q);
        assert r % p == (r * t * q) % p;
        assert (r * q) % p == 0;
        var rmod := r * t * q % p;
        assert rmod == r % p;
        assert rmod == r;
        assert (r * q) % p == 0;
        assert (r * q * t) % p == 0;
        assert (r * (q * t)) % p == 0;
        calc {
            r % p;
            == (r * 1) % p;
            == (r * (s * p + t * q)) % p;
            == (r * s * p + r * t * q) % p;
            == (r * t * q) % p;
            == ((r * q) * t) % p;
            == ((r * q) % p * (t % p)) % p;
            == (0 * (t % p)) % p;
            == 0;
        }
        assert r % p == 0;
        assert r == 0;
        assert false;
    }
}

lemma LcmDividesResult(a: int, b: int, m: int)
    requires a > 0 && b > 0 && m > 0
    requires m % a == 0 && m % b == 0
    ensures gcd(a, b) > 0
    ensures m % lcm(a, b) == 0
{
    GcdPos(a, b);
    GcdDividesA(a, b);
    GcdDividesB(a, b);
    var g := gcd(a, b);
    var ag := a / g;
    var bg := b / g;
    assert a == ag * g;
    assert b == bg * g;
    GcdScaleFactor(ag, bg, g);
    assert gcd(ag * g, bg * g) == gcd(ag, bg) * g;
    assert g == gcd(ag, bg) * g;
    assert gcd(ag, bg) == 1;
    var ka := m / a;
    var kb := m / b;
    assert m == ka * a;
    assert m == kb * b;
    assert m == ka * ag * g;
    assert m == kb * bg * g;
    assert ka * ag == kb * bg;
    var l := lcm(a, b);
    assert l == ag * b;
    assert l == ag * bg * g;
    assert (kb * bg) % ag == 0 by {
        assert kb * bg == ka * ag;
    }
    CoprimeDivides(ag, bg, kb);
    var fq := kb / ag;
    assert kb == fq * ag;
    assert m == fq * ag * bg * g;
    assert l == ag * bg * g;
    assert m == fq * l;
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
/* code modified by LLM (iteration 4): use lcm with proper lemma calls */
{
    var p10 := power(10, k);
    GcdPos(n, p10);
    var g := gcd(n, p10);
    GcdDividesA(n, p10);
    GcdDividesB(n, p10);
    var l := lcm(n, p10);
    result := l;
    assert result == n * p10 / g;
    assert result > 0 by {
        assert n > 0 && p10 > 0 && g > 0;
        var ng := n / g;
        assert ng > 0;
        assert result == ng * p10;
    }
    assert result % n == 0 by {
        var pg := p10 / g;
        assert result == n * pg;
    }
    assert result % p10 == 0 by {
        var ng := n / g;
        assert result == ng * p10;
    }
    forall m | m > 0 && m % n == 0 && m % p10 == 0
        ensures result <= m
    {
        LcmDividesResult(n, p10, m);
        assert m % result == 0;
        assert m >= result;
    }
}
// </vc-code>
