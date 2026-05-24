// <vc-preamble>
function min(a: int, b: int): int
    ensures min(a, b) == a || min(a, b) == b
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a ==> a <= b
    ensures min(a, b) == b ==> b <= a
{
    if a <= b then a else b
}

function computeInversions(n: int, k: int, iterations: int): int
    requires n >= 1 && k >= 0 && iterations >= 0
    requires iterations <= min(k, n / 2)
    decreases iterations
{
    if iterations == 0 then 0
    else computeInversions(n, k, iterations - 1) + (n - 2*(iterations-1) - 1) + (n - 2*(iterations-1) - 2)
}

function sumInversionsFormula(n: int, iterations: int): int
    requires n >= 1 && iterations >= 0
    requires iterations <= n / 2
    decreases iterations
{
    if iterations == 0 then 0
    else sumInversionsFormula(n, iterations - 1) + (n - 2*(iterations-1) - 1) + (n - 2*(iterations-1) - 2)
}

function sumOfConsecutivePairs(n: int, k: int): int
    requires n >= 1 && k >= 0 && k < n / 2
{
    var iterations := k;
    if iterations == 0 then 0
    else sumInversionsFormula(n, iterations)
}
// </vc-preamble>

// <vc-helpers>
lemma computeInversionsEqSumFormula(n: int, k: int, iterations: int)
    requires n >= 1 && k >= 0 && iterations >= 0
    requires iterations <= min(k, n / 2)
    ensures computeInversions(n, k, iterations) == sumInversionsFormula(n, iterations)
    decreases iterations
{
    if iterations == 0 {
    } else {
        computeInversionsEqSumFormula(n, k, iterations - 1);
    }
}

lemma sumFormulaTotal(n: int)
    requires n >= 1
    ensures sumInversionsFormula(n, n / 2) == n * (n - 1) / 2
    decreases n / 2
{
    var half := n / 2;
    sumFormulaTotalHelper(n, half);
}

lemma sumFormulaTotalHelper(n: int, iterations: int)
    requires n >= 1 && iterations >= 0 && iterations <= n / 2
    ensures sumInversionsFormula(n, iterations) == iterations * n - 2 * (iterations * (iterations - 1) / 2) - iterations + (iterations - 1) * iterations - iterations * (iterations - 1)
    decreases iterations
{
    if iterations == 0 {
    } else {
        sumFormulaTotalHelper(n, iterations - 1);
    }
}

lemma sumFormulaAtHalf(n: int)
    requires n >= 1
    ensures sumInversionsFormula(n, n / 2) == n * (n - 1) / 2
{
    var half := n / 2;
    sumFormulaAtHalfIter(n, half);
}

lemma sumFormulaAtHalfIter(n: int, iters: int)
    requires n >= 1 && iters == n / 2
    ensures sumInversionsFormula(n, iters) == n * (n - 1) / 2
    decreases iters
{
    if iters == 0 {
        assert n == 1 || n == 0;
    } else {
        sumFormulaAtHalfIter2(n, iters);
    }
}

lemma sumFormulaAtHalfIter2(n: int, iters: int)
    requires n >= 1 && iters == n / 2 && iters >= 1
    ensures sumInversionsFormula(n, iters) == n * (n - 1) / 2
    decreases iters
{
    sumFormulaClosedForm(n, iters);
}

lemma sumFormulaClosedForm(n: int, iters: int)
    requires n >= 1 && iters >= 0 && iters <= n / 2
    ensures sumInversionsFormula(n, iters) == 2 * iters * n - 2 * iters * iters - iters
    decreases iters
{
    if iters == 0 {
    } else {
        sumFormulaClosedForm(n, iters - 1);
        var prev := iters - 1;
        var contribution := (n - 2*prev - 1) + (n - 2*prev - 2);
        assert contribution == 2*n - 4*prev - 3;
        assert sumInversionsFormula(n, iters) == sumInversionsFormula(n, prev) + contribution;
        assert sumInversionsFormula(n, prev) == 2 * prev * n - 2 * prev * prev - prev;
        assert sumInversionsFormula(n, iters) == 2*prev*n - 2*prev*prev - prev + 2*n - 4*prev - 3;
        assert 2*prev*n - 2*prev*prev - prev + 2*n - 4*prev - 3 == 2*iters*n - 2*iters*iters - iters by {
            assert prev == iters - 1;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires n >= 1 && k >= 0
    ensures result >= 0
    ensures result == computeInversions(n, k, min(k, n / 2))
    ensures result == sumInversionsFormula(n, min(k, n / 2))
    ensures k >= n / 2 ==> result == n * (n - 1) / 2
    ensures k < n / 2 ==> result == sumOfConsecutivePairs(n, k)
// </vc-spec>
// <vc-code>
{
    var iterations := min(k, n / 2);
    var r := 0;
    var i := 0;
    while i < iterations
        invariant 0 <= i <= iterations
        invariant r == sumInversionsFormula(n, i)
        decreases iterations - i
    {
        r := r + (n - 2*i - 1) + (n - 2*i - 2);
        i := i + 1;
    }
    computeInversionsEqSumFormula(n, k, iterations);
    if k >= n / 2 {
        sumFormulaClosedForm(n, iterations);
        assert iterations == n / 2;
        assert r == 2 * iterations * n - 2 * iterations * iterations - iterations;
        var half := n / 2;
        if n % 2 == 0 {
            assert n == 2 * half;
            assert r == 2 * half * 2 * half - 2 * half * half - half;
            assert r == 4 * half * half - 2 * half * half - half;
            assert r == 2 * half * half - half;
            assert r == half * (2 * half - 1);
            assert r == (n / 2) * (n - 1);
            assert n * (n - 1) / 2 == (n / 2) * (n - 1);
        } else {
            assert n == 2 * half + 1;
            assert r == 2 * half * (2 * half + 1) - 2 * half * half - half;
            assert r == 4 * half * half + 2 * half - 2 * half * half - half;
            assert r == 2 * half * half + half;
            assert r == half * (2 * half + 1);
            assert r == (n / 2) * n;
            assert n * (n - 1) / 2 == n / 2 * n by {
                assert n % 2 == 1;
                assert (n - 1) % 2 == 0;
            }
        }
    }
    result := r;
}
// </vc-code>
