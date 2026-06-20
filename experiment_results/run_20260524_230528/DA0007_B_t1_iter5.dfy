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
/* helper modified by LLM (iteration 5): rewrote lemmas to avoid lambda matching issues */
lemma SeqEq(k: int, f: int -> int, g: int -> int)
    requires k >= 0
    requires forall i :: 0 <= i < k ==> f(i) == g(i)
    ensures seq(k, f) == seq(k, g)
{
    if k == 0 {
    } else {
        assert seq(k, f)[0] == f(0) == g(0) == seq(k, g)[0];
        var f' := (i: int) => f(i + 1);
        var g' := (i: int) => g(i + 1);
        SeqEq(k - 1, f', g');
        assert seq(k - 1, f') == seq(k - 1, g');
        assert seq(k, f)[1..] == seq(k - 1, f');
        assert seq(k, g)[1..] == seq(k - 1, g');
    }
}

lemma SumShiftByOne(k: int, offset: int)
    requires k >= 0
    ensures sum(seq(k, i => i + offset + 1)) == sum(seq(k, i => i + offset)) + k
    decreases k
{
    if k == 0 {
    } else {
        var s1 := seq(k, i => i + offset + 1);
        var s2 := seq(k, i => i + offset);
        assert s1[0] == offset + 1;
        assert s2[0] == offset;
        var f1 := (i: int) => (i + 1) + offset + 1;
        var f2 := (i: int) => (i + 1) + offset;
        var g1 := (i: int) => i + (offset + 1) + 1;
        var g2 := (i: int) => i + (offset + 1);
        SeqEq(k - 1, f1, g1);
        SeqEq(k - 1, f2, g2);
        assert seq(k - 1, f1) == seq(k - 1, g1);
        assert seq(k - 1, f2) == seq(k - 1, g2);
        assert s1[1..] == seq(k - 1, f1);
        assert s2[1..] == seq(k - 1, f2);
        SumShiftByOne(k - 1, offset + 1);
        assert sum(seq(k - 1, g1)) == sum(seq(k - 1, g2)) + (k - 1);
        assert sum(s1[1..]) == sum(s2[1..]) + (k - 1);
        assert sum(s1) == (offset + 1) + sum(s1[1..]);
        assert sum(s2) == offset + sum(s2[1..]);
    }
}

lemma SumOfInitialSeq(k: int)
    requires k >= 1
    ensures sum(seq(k, i => i + 1)) == k * (k + 1) / 2
    decreases k
{
    if k == 1 {
        assert seq(1, i => i + 1) == [1];
    } else {
        SumOfInitialSeq(k - 1);
        var s := seq(k, i => i + 1);
        assert s[0] == 1;
        var f := (i: int) => (i + 1) + 1;
        var g := (i: int) => i + 2;
        SeqEq(k - 1, f, g);
        assert s[1..] == seq(k - 1, f);
        assert seq(k - 1, f) == seq(k - 1, g);
        SumShiftByOne(k - 1, 1);
        var h := (i: int) => i + 1;
        assert seq(k - 1, h) == seq(k - 1, i => i + 1);
        assert sum(seq(k - 1, i => i + 2)) == sum(seq(k - 1, i => i + 1)) + (k - 1);
        assert sum(seq(k - 1, i => i + 1)) == (k - 1) * k / 2;
        assert sum(s[1..]) == (k - 1) * k / 2 + (k - 1);
        assert sum(s) == 1 + sum(s[1..]);
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
    /* code modified by LLM (iteration 5): use arithmetic to prove sum directly */
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
        assert forall j :: 0 <= j < k - 1 ==> sq[j] == j + 1;
        assert sq[k-1] == k + extra;
        assert extra >= 0;
        if k >= 2 {
            assert sq[k-2] == k - 1;
            assert sq[k-1] == k + extra;
            assert sq[k-2] < sq[k-1];
        }
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
        var baseSeq := seq(k, i => i + 1);
        SumOfInitialSeq(k);
        assert sum(baseSeq) == k * (k + 1) / 2;
        assert baseSeq == sq[k-1 := k] by {
            assert |baseSeq| == k;
            assert |sq[k-1 := k]| == k;
            forall j | 0 <= j < k ensures baseSeq[j] == sq[k-1 := k][j] {
                if j < k - 1 {
                    assert baseSeq[j] == j + 1;
                    assert sq[k-1 := k][j] == sq[j];
                    assert sq[j] == j + 1;
                } else {
                    assert baseSeq[j] == k;
                    assert sq[k-1 := k][j] == k;
                }
            }
        }
        SumUpdate(sq, k-1, k + extra, k);
        assert sum(sq[k-1 := k]) == sumVal - (k + extra) + k;
        assert sum(baseSeq) == sumVal - extra;
        assert sumVal == k * (k + 1) / 2 + extra;
        assert sumVal == n;
        result := sq;
    }
}
// </vc-code>
