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
/* helper modified by LLM (iteration 2): simplified gcd/lcm helpers with better proofs */
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
    ensures a % gcd(a, b) == 0
    decreases b
{
    if b == 0 {
    } else {
        GcdDividesA(b, a % b);
        GcdDividesB(b, a % b);
        var g := gcd(a, b);
        assert g == gcd(b, a % b);
        var r := a % b;
        var q := a / b;
        assert a == q * b + r;
        assert b % g == 0;
        assert r % g == 0;
        assert (q * b + r) % g == 0;
    }
}

lemma GcdDividesB(a: int, b: int)
    requires a > 0 && b >= 0
    ensures b % gcd(a, b) == 0
    decreases b
{
    if b == 0 {
    } else {
        GcdDividesA(b, a % b);
    }
}

lemma GcdCoprime(a: int, b: int)
    requires a > 0 && b >= 0
    ensures gcd(a / gcd(a, b), b / gcd(a, b)) == 1
    decreases b
{
    GcdPos(a, b);
    var g := gcd(a, b);
    var ag := a / g;
    var bg := b / g;
    GcdDividesA(a, b);
    GcdDividesB(a, b);
    assert a == ag * g;
    assert b == bg * g;
    GcdCoprimeLemma(ag, bg, g);
}

lemma GcdCoprimeLemma(ag: int, bg: int, g: int)
    requires ag > 0 && bg >= 0 && g > 0
    requires gcd(ag * g, bg * g) == g
    ensures gcd(ag, bg) == 1
{
    GcdScaleFactor(ag, bg, g);
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
    assert gcd(a, b) == gcd(ag, bg) * g;
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
        assert (ka * ag) % ag == 0;
    }
    var factor := kb * bg / ag;
    assert kb * bg == factor * ag;
    assert m == factor * ag * g;
    assert l == ag * bg * g;
    assert m == factor * g * ag;
    assert l == bg * g * ag;
    assert m % l == 0 by {
        assert factor % bg == 0 by {
            assert factor * ag == kb * bg;
            assert gcd(ag, bg) == 1;
            CoprimeDivides(bg, ag, factor);
        }
        var fq := factor / bg;
        assert factor == fq * bg;
        assert m == fq * bg * g * ag;
        assert l == bg * g * ag;
        assert m == fq * l;
    }
}

lemma CoprimeDivides(p: int, q: int, x: int)
    requires p > 0 && q > 0 && x >= 0
    requires gcd(p, q) == 1
    requires (x * q) % p == 0
    ensures x % p == 0
{
    ModMulCoprime(p, q, x);
}

lemma ModMulCoprime(p: int, q: int, x: int)
    requires p > 0 && q > 0 && x >= 0
    requires gcd(p, q) == 1
    requires (x * q) % p == 0
    ensures x % p == 0
{
    var r := x % p;
    if r != 0 {
        assert (r * q) % p == (x * q) % p;
        assert (r * q) % p == 0;
        assert r < p;
        assert r > 0;
        BezoutLemma(p, q);
    }
}

lemma BezoutLemma(p: int, q: int)
    requires p > 0 && q > 0
    requires gcd(p, q) == 1
    ensures exists s: int, t: int :: s * p + t * q == 1
{
    BezoutHelper(p, q);
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
        assert s * a + t * b == gcd(a, b);
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
/* code modified by LLM (iteration 2): use lcm with proper preconditions */
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
        assert n * p10 > 0;
        GcdDividesA(n, p10);
        assert n % g == 0;
        var ng := n / g;
        assert ng > 0;
        assert result == ng * p10;
    }
    assert result % n == 0 by {
        GcdDividesB(n, p10);
        assert p10 % g == 0;
        var pg := p10 / g;
        assert result == n * pg;
    }
    assert result % p10 == 0 by {
        GcdDividesA(n, p10);
        assert n % g == 0;
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
