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
function gcd(a: int, b: int): int
    requires a > 0 && b >= 0
    decreases b
{
    if b == 0 then a else gcd(b, a % b)
}

function lcm(a: int, b: int): int
    requires a > 0 && b > 0
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
    if b == 0 {} else {
        GcdDividesA(b, a % b);
        var g := gcd(b, a % b);
        var q := a / b;
        var r := a % b;
        assert a == q * b + r;
        GcdDividesB(b, a % b);
    }
}

lemma GcdDividesB(a: int, b: int)
    requires a > 0 && b >= 0
    ensures b % gcd(a, b) == 0
    decreases b
{
    if b == 0 {} else {
        GcdDividesA(b, a % b);
    }
}

lemma LcmDividesResult(a: int, b: int, m: int)
    requires a > 0 && b > 0 && m > 0
    requires m % a == 0 && m % b == 0
    ensures m % lcm(a, b) == 0
{
    GcdPos(a, b);
    GcdDividesA(a, b);
    GcdDividesB(a, b);
    var g := gcd(a, b);
    var l := lcm(a, b);
    assert l == a * b / g;
    var ka := m / a;
    var kb := m / b;
    assert m == ka * a;
    assert m == kb * b;
    assert a % g == 0;
    assert b % g == 0;
    var ag := a / g;
    var bg := b / g;
    assert a == ag * g;
    assert b == bg * g;
    assert l == ag * b;
    assert l == ag * bg * g;
    assert m == ka * ag * g;
    assert kb * bg * g == ka * ag * g;
    assert kb * bg == ka * ag;
    assert m % l == 0 by {
        assert m == kb * b;
        assert b == bg * g;
        assert l == ag * b;
        assert ka * ag == kb * bg;
        calc {
            m;
            == kb * b;
            == kb * bg * g;
            == ka * ag * g;
        }
        assert m / l == kb / ag by {
            assert m == kb * ag * b / ag;
        }
        assert ag * bg == l / g;
        assert m == kb * bg * g;
        assert l == ag * bg * g;
        assert m % l == 0 by {
            assert (kb * bg * g) % (ag * bg * g) == 0 by {
                assert kb * bg == ka * ag;
                assert (ka * ag) % ag == 0;
                assert (kb * bg) % ag == 0;
                assert (kb * bg * g) % (ag * g) == 0;
                assert ag * bg * g > 0;
                var factor := kb * bg / ag;
                assert kb * bg == factor * ag;
                assert m == factor * ag * g;
                assert l == ag * bg * g;
                assert m == factor * (g * ag);
                assert l == bg * (g * ag);
                assert m % l == 0 by {
                    assert factor % bg == 0 by {
                        assert factor * ag == kb * bg;
                    }
                }
            }
        }
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
{
    var p10 := power(10, k);
    GcdPos(n, p10);
    var g := gcd(n, p10);
    var l := lcm(n, p10);
    GcdDividesA(n, p10);
    GcdDividesB(n, p10);
    assert l == n * p10 / g;
    assert n % g == 0;
    assert p10 % g == 0;
    result := l;
    assert result > 0 by {
        assert n > 0 && p10 > 0 && g > 0;
        assert result == n * p10 / g;
        assert n * p10 > 0;
        assert n * p10 >= g;
    }
    assert result % n == 0 by {
        assert result == n * (p10 / g);
    }
    assert result % p10 == 0 by {
        assert result == p10 * (n / g);
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
