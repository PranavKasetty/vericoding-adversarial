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
    if b == 0 then a
    else gcd(b, a % b)
}

function lcm(a: int, b: int): int
    requires a > 0 && b > 0
{
    a * b / gcd(a, b)
}

lemma gcd_divides_both(a: int, b: int)
    requires a > 0 && b >= 0
    ensures a % gcd(a, b) == 0
    ensures b % gcd(a, b) == 0
    decreases b
{
    if b == 0 {
    } else {
        gcd_divides_both(b, a % b);
        var g := gcd(b, a % b);
        assert b % g == 0;
        assert (a % b) % g == 0;
        assert a == (a / b) * b + (a % b);
    }
}

lemma gcd_positive(a: int, b: int)
    requires a > 0 && b >= 0
    ensures gcd(a, b) > 0
    decreases b
{
    if b == 0 {
    } else {
        gcd_positive(b, a % b);
    }
}

lemma lcm_multiples(a: int, b: int)
    requires a > 0 && b > 0
    ensures lcm(a, b) % a == 0
    ensures lcm(a, b) % b == 0
{
    gcd_divides_both(a, b);
    gcd_positive(a, b);
    var g := gcd(a, b);
    assert a % g == 0;
    assert b % g == 0;
    var l := a * b / g;
    assert l == a * (b / g);
    assert l % a == 0;
    assert l == b * (a / g);
    assert l % b == 0;
}

lemma lcm_positive(a: int, b: int)
    requires a > 0 && b > 0
    ensures lcm(a, b) > 0
{
    gcd_positive(a, b);
    var g := gcd(a, b);
    assert g > 0;
    assert g <= a;
    assert a * b / g >= 1;
}

lemma gcd_divides_common(a: int, b: int, c: int)
    requires a > 0 && b >= 0 && c > 0
    requires c % a == 0 && c % b == 0
    ensures c % gcd(a, b) == 0
    decreases b
{
    if b == 0 {
    } else {
        var r := a % b;
        assert c % b == 0;
        assert a == (a / b) * b + r;
        assert r == a - (a / b) * b;
        assert c % r == 0 by {
            assert c % a == 0;
            assert c % b == 0;
            var qa := c / a;
            var qb := c / b;
            assert c == qa * a;
            assert c == qb * b;
            assert r * (c / r) == c - (a/b) * c % b by {
            }
            // r = a mod b, so r = a - (a/b)*b
            // c mod r: c = qa*a, r = a - (a/b)*b
            // We need c % r == 0
            // c = qa * a = qa * ((a/b)*b + r) = qa*(a/b)*b + qa*r
            // c % r == (qa*(a/b)*b + qa*r) % r == (qa*(a/b)*b) % r
            // b % r: b = qb_inner * r + b%r ... this gets complicated
            // Let's use the fact that gcd(a,b) = gcd(b, a%b)
            // and any common divisor of a and b divides gcd(a,b)
            // Actually we want: if c%a==0 and c%b==0 then c%(a%b)==0
            assert a % b == r;
            assert c % a == 0;
            assert c % b == 0;
            // c = k1*a, c = k2*b
            // r = a - (a/b)*b
            // c % r: we need to show r | c
            // k1*a = k2*b => k1*(q*b+r) = k2*b => k1*q*b + k1*r = k2*b
            // k1*r = (k2 - k1*q)*b
            // So r | k1*r means r | (k2-k1*q)*b
            // Hmm this doesn't directly give r | c
            // Let's try: gcd(a,b) | a and gcd(a,b) | b => gcd(a,b) | r
            // c % gcd(a,b) == 0 since gcd(a,b)|a and gcd(a,b)|b... wait that's circular
        }
        gcd_divides_common(b, a % b, c);
    }
}

lemma lcm_is_minimum(a: int, b: int, c: int)
    requires a > 0 && b > 0 && c > 0
    requires c % a == 0 && c % b == 0
    ensures lcm(a, b) <= c
{
    gcd_positive(a, b);
    gcd_divides_both(a, b);
    var g := gcd(a, b);
    var l := lcm(a, b);
    // l = a*b/g
    // c is divisible by a and b
    // We need l <= c, i.e., l | c
    // c % a == 0, c % b == 0
    // Let a = g*a', b = g*b' where gcd(a',b')=1
    // l = g*a'*b'
    // c = k*a = k*g*a' for some k, so g*a' | c
    // c = m*b = m*g*b' for some m, so g*b' | c  
    // k*g*a' = m*g*b' => k*a' = m*b'
    // since gcd(a',b')=1, b' | k
    // so c = k*g*a' = (b'*j)*g*a' = j*g*a'*b' = j*l
    // hence l | c, so l <= c
    lcm_multiples(a, b);
    lcm_positive(a, b);
    // We'll prove l | c
    assert c % l == 0 by {
        // a = g * (a/g), b = g * (b/g)
        var ag := a / g;
        var bg := b / g;
        assert a == g * ag;
        assert b == g * bg;
        // gcd(ag, bg) == 1 -- hard to prove in Dafny without more lemmas
        // l = a * bg = b * ag
        assert l == a * bg;
        assert l == b * ag;
        // c = qa * a for some qa
        var qa := c / a;
        assert c == qa * a;
        // c = qb * b for some qb  
        var qb := c / b;
        assert c == qb * b;
        // c = qa * g * ag = qb * g * bg
        // qa * ag = qb * bg
        // since gcd(ag,bg)=1, bg | qa
        // c = qa * a = (bg * t) * g * ag = t * l
        // We need to show c % l == 0
        // c / l = c / (a * bg) = (c/a) / bg = qa / bg
        // We need bg | qa
        // qa * ag = qb * bg ... bg | qa * ag
        // If gcd(ag,bg)=1 then bg | qa
        // Let's just verify numerically that c % l == 0
        // Actually in Dafny we can't easily prove gcd(ag,bg)=1
        // Let me use a different approach
        // We know l = a*b/g
        // c % a == 0 means a | c
        // c % b == 0 means b | c
        // c / g is divisible by a/g and b/g
        // Hmm, let me try to use modular arithmetic directly
        assert c * g % (a * b) == 0 by {
            // c = qa*a, so c*g = qa*a*g
            // a*b = a*b
            // qa*a*g % (a*b) == 0 iff qa*g % b == 0
            // qa*a = c, c%b==0, so b | c = qa*a
            // b | qa*a means qa*a % b == 0
            // g | b (g divides b), b = g*bg
            // qa*a % b == 0
            // qa * g * ag % (g * bg) == 0
            // qa * ag % bg == 0
            // We need bg | qa*ag
            // From qa*ag = qb*bg we get bg | qa*ag
            assert qa * ag == qb * bg;
            assert (qa * ag) % bg == 0;
            // since ag and bg might not be coprime we can't directly conclude
            // But (qa*ag) % bg == 0 means bg | qa*ag
            assert qa * g * ag % (g * bg) == 0;
            assert c * g % (a * b) == 0;
        }
        assert c % (a * b / g) == 0;
    }
    assert l <= c;
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
    var p10k := power(10, k);
    var ans := lcm(n, p10k);
    lcm_positive(n, p10k);
    lcm_multiples(n, p10k);
    assert ans % n == 0;
    assert ans % p10k == 0;
    forall m | m > 0 && m % n == 0 && m % p10k == 0
        ensures ans <= m
    {
        lcm_is_minimum(n, p10k, m);
    }
    result := ans;
}
// </vc-code>
