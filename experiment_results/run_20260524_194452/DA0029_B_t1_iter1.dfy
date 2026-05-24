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

lemma sumFormulaFullValue(n: int)
    requires n >= 1
    ensures sumInversionsFormula(n, n / 2) == n * (n - 1) / 2
{
    var half := n / 2;
    sumFormulaValue(n, half);
}

lemma sumFormulaValue(n: int, iters: int)
    requires n >= 1 && iters >= 0 && iters <= n / 2
    ensures sumInversionsFormula(n, iters) == iters * (2 * n - 1) - 2 * iters * iters
    decreases iters
{
    if iters == 0 {
    } else {
        sumFormulaValue(n, iters - 1);
        var prev := iters - 1;
        // sumInversionsFormula(n, iters) = sumInversionsFormula(n, prev) + (n - 2*prev - 1) + (n - 2*prev - 2)
        // = prev*(2*n-1) - 2*prev*prev + (2*n - 4*prev - 3)
        // = prev*(2*n-1) - 2*prev*prev + 2*n - 4*prev - 3
        // iters*(2*n-1) - 2*iters*iters
        // = (prev+1)*(2*n-1) - 2*(prev+1)*(prev+1)
        // = prev*(2*n-1) + (2*n-1) - 2*(prev*prev + 2*prev + 1)
        // = prev*(2*n-1) + 2*n - 1 - 2*prev*prev - 4*prev - 2
        // = prev*(2*n-1) - 2*prev*prev + 2*n - 4*prev - 3
        // matches!
    }
}

lemma minKGeHalfMeansFullSum(n: int, k: int)
    requires n >= 1 && k >= 0
    requires k >= n / 2
    ensures min(k, n / 2) == n / 2
{
}

lemma minKLtHalfMeansK(n: int, k: int)
    requires n >= 1 && k >= 0
    requires k < n / 2
    ensures min(k, n / 2) == k
{
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
    
    // Prove computeInversions == sumInversionsFormula
    computeInversionsEqSumFormula(n, k, iterations);
    
    // Compute the result iteratively
    result := 0;
    var i := 0;
    while i < iterations
        invariant 0 <= i <= iterations
        invariant result == sumInversionsFormula(n, i)
    {
        result := result + (n - 2*i - 1) + (n - 2*i - 2);
        i := i + 1;
    }
    
    // Prove the conditional postconditions
    if k >= n / 2 {
        minKGeHalfMeansFullSum(n, k);
        sumFormulaFullValue(n);
    } else {
        minKLtHalfMeansK(n, k);
    }
}
// </vc-code>
