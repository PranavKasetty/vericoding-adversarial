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
/* helper modified by LLM (iteration 2): fixed lemmas for sumInversionsFormula closed form and total */
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

lemma sumFormulaNonNeg(n: int, iters: int)
    requires n >= 1 && iters >= 0 && iters <= n / 2
    ensures sumInversionsFormula(n, iters) >= 0
{
    sumFormulaClosedForm(n, iters);
    var half := n / 2;
    assert iters <= half;
    assert 2 * iters * n - 2 * iters * iters - iters == iters * (2 * n - 2 * iters - 1);
    assert 2 * n - 2 * iters - 1 >= 0 by {
        assert iters <= n / 2;
        assert 2 * iters <= n;
        assert 2 * n - 2 * iters - 1 >= n - 1 >= 0;
    }
}

lemma sumFormulaTotal(n: int)
    requires n >= 1
    ensures sumInversionsFormula(n, n / 2) == n * (n - 1) / 2
{
    var half := n / 2;
    sumFormulaClosedForm(n, half);
    assert sumInversionsFormula(n, half) == 2 * half * n - 2 * half * half - half;
    if n % 2 == 0 {
        assert n == 2 * half;
        assert 2 * half * n - 2 * half * half - half == 2 * half * 2 * half - 2 * half * half - half;
        assert 2 * half * 2 * half - 2 * half * half - half == 2 * half * half - half;
        assert 2 * half * half - half == half * (2 * half - 1);
        assert n * (n - 1) / 2 == 2 * half * (2 * half - 1) / 2;
        assert 2 * half * (2 * half - 1) / 2 == half * (2 * half - 1);
    } else {
        assert n == 2 * half + 1;
        assert 2 * half * n - 2 * half * half - half == 2 * half * (2 * half + 1) - 2 * half * half - half;
        assert 2 * half * (2 * half + 1) - 2 * half * half - half == half * (2 * half + 1);
        assert n * (n - 1) / 2 == (2 * half + 1) * (2 * half) / 2;
        assert (2 * half + 1) * (2 * half) / 2 == half * (2 * half + 1);
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
/* code modified by LLM (iteration 2): use lemmas to establish all postconditions */
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
    sumFormulaNonNeg(n, iterations);
    if k >= n / 2 {
        sumFormulaClosedForm(n, iterations);
        sumFormulaTotal(n);
        assert iterations == n / 2;
    }
    result := r;
}
// </vc-code>
