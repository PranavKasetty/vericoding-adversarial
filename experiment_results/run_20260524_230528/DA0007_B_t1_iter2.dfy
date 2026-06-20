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
    } else {
        var s := seq(k, i => i + 1);
        assert s[0] == 1;
        assert s[1..] == seq(k - 1, i => i + 2);
        SumShiftLemmaGeneral(k - 1, 1);
        SumOfInitialSeq(k - 1);
    }
}

/* helper modified by LLM (iteration 2): generalized shift lemma to handle arbitrary offsets */
lemma SumShiftLemmaGeneral(k: int, offset: int)
    requires k >= 1
    ensures sum(seq(k, i => i + offset + 1)) == sum(seq(k, i => i + offset)) + k
    decreases k
{
    if k == 1 {
        assert seq(1, i => i + offset + 1) == [offset + 1];
        assert seq(1, i => i + offset) == [offset];
    } else {
        var s1 := seq(k, i => i + offset + 1);
        var s2 := seq(k, i => i + offset);
        assert s1[0] == offset + 1;
        assert s2[0] == offset;
        assert s1[1..] == seq(k-1, i => i + offset + 2);
        assert s2[1..] == seq(k-1, i => i + offset + 1);
        SumShiftLemmaGeneral(k - 1, offset + 1);
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

lemma SumUpdate(s: seq<int>, idx: int, oldVal: int, newVal: int)
    requires 0 <= idx < |s|
    requires s[idx] == oldVal
    ensures sum(s[idx := newVal]) == sum(s) - oldVal + newVal
    decreases idx
{
    if idx == 0 {
        assert s[idx := newVal][1..] == s[1..];
    } else {
        var s2 := s[idx := newVal];
        assert s2[0] == s[0];
        assert s2[1..] == s[1..][idx-1 := newVal];
        SumUpdate(s[1..], idx - 1, oldVal, newVal);
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
    /* code modified by LLM (iteration 2): use arithmetic to prove sum directly */
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
        var oldLast := s[k-1];
        s[k - 1] := k + extra;
        var sq := s[..];
        // Prove AllPositive
        assert forall j :: 0 <= j < k - 1 ==> sq[j] == j + 1;
        assert sq[k-1] == k + extra;
        assert extra >= 0;
        // Prove IsStrictlyIncreasing
        assert forall j :: 0 <= j < k - 1 ==> sq[j] == j + 1;
        assert forall j :: 0 <= j < k - 2 ==> sq[j] < sq[j+1];
        if k >= 2 {
            assert sq[k-2] == k - 1;
            assert sq[k-1] == k + extra;
            assert sq[k-2] < sq[k-1];
        }
        // Prove sum using loop with invariant tracking arithmetic sum
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
        // Now prove sumVal == n
        // sq = [1, 2, ..., k-1, k+extra]
        // sum = (1 + 2 + ... + (k-1)) + (k + extra)
        // = (k-1)*k/2 + k + extra
        // = k*(k+1)/2 + extra = k*(k+1)/2 + n - k*(k+1)/2 = n
        var baseSeq := seq(k, i => i + 1);
        SumOfInitialSeq(k);
        assert sum(baseSeq) == k * (k + 1) / 2;
        // sq == baseSeq[k-1 := k + extra]
        assert baseSeq == sq[k-1 := k];
        SumUpdate(sq, k-1, k + extra, k);
        assert sum(sq[k-1 := k]) == sumVal - (k + extra) + k;
        assert sq[k-1 := k] == baseSeq;
        assert sumVal == n;
        result := sq;
    }
}
// </vc-code>
