// <vc-preamble>
predicate ValidInput(n: int, k: int)
{
    n > 0 && k > 0
}

predicate IsStrictlyIncreasing(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i+1]
}

predicate AllPositive(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] > 0
}

function sum(s: seq<int>): int
    decreases |s|
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

predicate ValidSequence(s: seq<int>, n: int, k: int)
{
    |s| == k && AllPositive(s) && IsStrictlyIncreasing(s) && sum(s) == n
}

predicate IsPossible(n: int, k: int)
{
    k * (k + 1) / 2 <= n
}
// </vc-preamble>

// <vc-helpers>
// Helper lemmas for sequence construction
lemma SumOfRange(k: int)
    requires k >= 1
    ensures sum(seq(k, i => i + 1)) == k * (k + 1) / 2
{
    if k == 1 {
    } else {
        SumOfRange(k - 1);
    }
}

lemma SeqWithLastReplaced(s: seq<int>, v: int)
    requires |s| >= 1
    ensures s[..|s|-1] + [v] == s[..|s|-1] + [v]
{
}

function buildBase(k: int): seq<int>
    requires k >= 1
    ensures |buildBase(k)| == k
    ensures forall i :: 0 <= i < k ==> buildBase(k)[i] == i + 1
    decreases k
{
    if k == 1 then [1] else buildBase(k-1) + [k]
}

lemma buildBaseStrictlyIncreasing(k: int)
    requires k >= 1
    ensures IsStrictlyIncreasing(buildBase(k))
    decreases k
{
    if k == 1 {
    } else {
        buildBaseStrictlyIncreasing(k - 1);
        var s := buildBase(k);
        var prev := buildBase(k - 1);
        assert s == prev + [k];
        forall i | 0 <= i < |s| - 1
            ensures s[i] < s[i+1]
        {
            if i < |prev| - 1 {
                assert s[i] == prev[i];
                assert s[i+1] == prev[i+1];
            } else if i == |prev| - 1 {
                assert s[i] == prev[i] == k - 1;
                assert s[i+1] == k;
            }
        }
    }
}

lemma buildBaseSum(k: int)
    requires k >= 1
    ensures sum(buildBase(k)) == k * (k + 1) / 2
    decreases k
{
    if k == 1 {
    } else {
        buildBaseSum(k - 1);
        var s := buildBase(k);
        var prev := buildBase(k - 1);
        assert s == prev + [k];
        SumAppend(prev, [k]);
    }
}

lemma SumAppend(a: seq<int>, b: seq<int>)
    ensures sum(a + b) == sum(a) + sum(b)
    decreases |a|
{
    if |a| == 0 {
        assert a + b == b;
    } else {
        assert (a + b)[1..] == a[1..] + b;
        SumAppend(a[1..], b);
    }
}

lemma buildBaseAllPositive(k: int)
    requires k >= 1
    ensures AllPositive(buildBase(k))
    decreases k
{
    if k == 1 {
    } else {
        buildBaseAllPositive(k - 1);
        var s := buildBase(k);
        var prev := buildBase(k - 1);
        assert s == prev + [k];
        forall i | 0 <= i < |s| ensures s[i] > 0 {
            if i < |prev| {
                assert s[i] == prev[i];
            } else {
                assert s[i] == k;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, k)
    ensures (|result| == 1 && result[0] == -1) || 
            (ValidSequence(result, n, k))
    ensures (|result| == 1 && result[0] == -1) <==> !IsPossible(n, k)
// </vc-spec>
// <vc-code>
{
    if !IsPossible(n, k) {
        result := [-1];
    } else {
        var base := buildBase(k);
        buildBaseSum(k);
        buildBaseStrictlyIncreasing(k);
        buildBaseAllPositive(k);
        var extra := n - k * (k + 1) / 2;
        var last := base[k-1] + extra;
        result := base[..k-1] + [last];
        SumAppend(base[..k-1], [last]);
        SumAppend(base[..k-1], [base[k-1]]);
        assert base[..k-1] + [base[k-1]] == base;
        assert sum(base[..k-1]) + base[k-1] == k * (k + 1) / 2;
        assert sum(result) == sum(base[..k-1]) + last;
        assert sum(result) == sum(base[..k-1]) + base[k-1] + extra;
        assert sum(result) == n;
        forall i | 0 <= i < |result| - 1 ensures result[i] < result[i+1] {
            if i < k - 2 {
                assert result[i] == base[i];
                assert result[i+1] == base[i+1];
            } else {
                assert result[i] == base[k-2];
                assert result[i+1] == last;
                assert last == k + extra;
                assert k + extra >= k > k - 1 == base[k-2];
            }
        }
        forall i | 0 <= i < |result| ensures result[i] > 0 {
            if i < k - 1 {
                assert result[i] == base[i];
            } else {
                assert result[i] == last;
                assert last >= k > 0;
            }
        }
    }
}
// </vc-code>
