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
lemma SumOfInitialSeq(k: int)
    requires k >= 1
    ensures sum(seq(k, i => i + 1)) == k * (k + 1) / 2
    decreases k
{
    if k == 1 {
        assert seq(1, i => i + 1) == [1];
        assert sum([1]) == 1;
    } else {
        var s := seq(k, i => i + 1);
        var s' := seq(k - 1, i => i + 1);
        assert s[0] == 1;
        assert s[1..] == seq(k - 1, i => i + 2);
        SumShiftLemma(k - 1);
        SumOfInitialSeq(k - 1);
    }
}

lemma SumShiftLemma(k: int)
    requires k >= 1
    ensures sum(seq(k, i => i + 2)) == sum(seq(k, i => i + 1)) + k
    decreases k
{
    if k == 1 {
        assert seq(1, i => i + 2) == [2];
        assert seq(1, i => i + 1) == [1];
    } else {
        var s1 := seq(k, i => i + 2);
        var s2 := seq(k, i => i + 1);
        assert s1[0] == 2;
        assert s2[0] == 1;
        assert s1[1..] == seq(k-1, i => i + 3);
        assert s2[1..] == seq(k-1, i => i + 2);
        SumShiftLemma(k - 1);
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
        var s := new int[k];
        var i := 0;
        while i < k
            invariant 0 <= i <= k
            invariant forall j :: 0 <= j < i ==> s[j] == j + 1
        {
            s[i] := i + 1;
            i := i + 1;
        }
        var extra := n - k * (k + 1) / 2;
        s[k - 1] := k + extra;
        var sq := s[..];
        // Prove AllPositive
        assert forall j :: 0 <= j < k - 1 ==> sq[j] == j + 1 > 0;
        assert sq[k-1] == k + extra;
        assert extra >= 0;
        assert sq[k-1] >= k >= 1;
        // Prove IsStrictlyIncreasing
        assert forall j :: 0 <= j < k - 1 ==> sq[j] == j + 1;
        assert forall j :: 0 <= j < k - 2 ==> sq[j] < sq[j+1];
        assert k >= 2 ==> sq[k-2] == k - 1 < k <= k + extra == sq[k-1];
        // Prove sum
        var sumVal := 0;
        var idx := 0;
        while idx < k
            invariant 0 <= idx <= k
            invariant sumVal == sum(sq[..idx])
        {
            assert sq[..idx+1] == sq[..idx] + [sq[idx]];
            SumAppend(sq[..idx], sq[idx]);
            sumVal := sumVal + sq[idx];
            idx := idx + 1;
        }
        assert sq[..k] == sq;
        assert sumVal == n;
        result := sq;
    }
}

lemma SumAppend(s: seq<int>, x: int)
    ensures sum(s + [x]) == sum(s) + x
    decreases |s|
{
    if |s| == 0 {
        assert s + [x] == [x];
    } else {
        assert (s + [x])[1..] == s[1..] + [x];
        SumAppend(s[1..], x);
    }
}
// </vc-code>
