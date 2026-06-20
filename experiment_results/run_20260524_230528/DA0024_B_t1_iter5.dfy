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
/* helper modified by LLM (iteration 5): simplified all lemma proofs to avoid timeouts */
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
    a / gcd(a, b) * b
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
        var g := gcd(a, b);
        assert g == gcd(b, a % b);
        var q := a / b;
        var r := a % b;
        assert a == q * b + r;
        assert b % g == 0;
        assert r % g == 0;
        assert q * b % g == 0;
        assert (q * b + r) % g == 0;
    }
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

lemma LcmPos(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
    ensures lcm(a, b) > 0
{
    GcdPos(a, b);
    GcdDividesA(a, b);
    var g := gcd(a, b);
    var ag := a / g;
    assert a == ag * g;
    assert ag > 0;
    assert lcm(a, b) == ag * b;
    assert ag * b > 0;
}

lemma LcmDividesA(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
    ensures lcm(a, b) % a == 0
{
    GcdPos(a, b);
    GcdDividesA(a, b);
    GcdDividesB(a, b);
    var g := gcd(a, b);
    var ag := a / g;
    var bg := b / g;
    assert a == ag * g;
    assert b == bg * g;
    assert lcm(a, b) == ag * b;
    assert ag * b == ag * bg * g;
    assert a == ag * g;
    assert ag * b % a == 0;
}

lemma LcmDividesB(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
    ensures lcm(a, b) % b == 0
{
    GcdPos(a, b);
    GcdDividesA(a, b);
    var g := gcd(a, b);
    var ag := a / g;
    assert lcm(a, b) == ag * b;
    assert ag * b % b == 0;
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
    assert x == x * (s * p + t * q);
    assert x == x * s * p + x * t * q;
    assert (x * t * q) % p == 0;
    assert x % p == (x * s * p + x * t * q) % p;
    assert x % p == (x * t * q) % p;
    assert x % p == 0;
}

lemma LcmDividesResult(a: int, b: int, m: int)
    requires a > 0 && b > 0 && m > 0
    requires m % a == 0 && m % b == 0
    ensures gcd(a, b) > 0
    ensures lcm(a, b) > 0
    ensures m % lcm(a, b) == 0
{
    GcdPos(a, b);
    GcdDividesA(a, b);
    GcdDividesB(a, b);
    LcmPos(a, b);
    var g := gcd(a, b);
    var ag := a / g;
    var bg := b / g;
    assert a == ag * g;
    assert b == bg * g;
    assert gcd(ag * g, bg * g) == gcd(ag, bg) * g by {
        GcdScaleFactor(ag, bg, g);
    }
    assert gcd(ag, bg) == 1;
    var ka := m / a;
    var kb := m / b;
    assert m == ka * a;
    assert m == kb * b;
    assert m == ka * ag * g;
    assert m == kb * bg * g;
    assert ka * ag == kb * bg;
    assert lcm(a, b) == ag * b;
    assert lcm(a, b) == ag * bg * g;
    assert (kb * bg) % ag == 0;
    CoprimeDivides(ag, bg, kb);
    var fq := kb / ag;
    assert kb == fq * ag;
    assert m == fq * ag * bg * g;
    assert m == fq * lcm(a, b);
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
/* code modified by LLM (iteration 5): use lcm with proper lemma calls */
{
    var p10 := power(10, k);
    GcdPos(n, p10);
    GcdDividesA(n, p10);
    GcdDividesB(n, p10);
    LcmPos(n, p10);
    LcmDividesA(n, p10);
    LcmDividesB(n, p10);
    var l := lcm(n, p10);
    result := l;
    assert result > 0;
    assert result % n == 0;
    assert result % p10 == 0;
    forall m | m > 0 && m % n == 0 && m % p10 == 0
        ensures result <= m
    {
        LcmDividesResult(n, p10, m);
        assert m % result == 0;
        assert m >= result;
    }
}
// </vc-code>
