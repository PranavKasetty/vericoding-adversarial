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
/* helper modified by LLM (iteration 4): fixed arithmetic steps in recursive proofs */
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
        var t := seq(k - 1, i => i + 2);
        assert s[1..] == t by {
            assert |s[1..]| == k - 1;
            assert |t| == k - 1;
            forall j | 0 <= j < k - 1 ensures s[1..][j] == t[j] {
                assert s[1..][j] == s[j+1];
                assert s[j+1] == (j+1) + 1;
                assert t[j] == j + 2;
            }
        }
        SumShiftLemmaGeneral(k - 1, 1);
        SumOfInitialSeq(k - 1);
        assert sum(seq(k-1, i => i + 2)) == sum(seq(k-1, i => i + 1)) + (k-1);
        assert sum(seq(k-1, i => i + 1)) == (k-1) * k / 2;
        assert sum(t) == (k-1) * k / 2 + (k-1);
        assert sum(s) == 1 + sum(t);
        assert sum(s) == 1 + (k-1) * k / 2 + (k-1);
        assert 1 + (k-1) * k / 2 + (k-1) == k * (k + 1) / 2;
    }
}

/* helper modified by LLM (iteration 4): fixed arithmetic in recursive case */
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
        var t1 := seq(k-1, i => i + offset + 2);
        var t2 := seq(k-1, i => i + offset + 1);
        assert s1[1..] == t1 by {
            assert |s1[1..]| == k - 1;
            assert |t1| == k - 1;
            forall j | 0 <= j < k - 1 ensures s1[1..][j] == t1[j] {
                assert s1[1..][j] == s1[j+1];
                assert s1[j+1] == (j+1) + offset + 1;
                assert t1[j] == j + offset + 2;
            }
        }
        assert s2[1..] == t2 by {
            assert |s2[1..]| == k - 1;
            assert |t2| == k - 1;
            forall j | 0 <= j < k - 1 ensures s2[1..][j] == t2[j] {
                assert s2[1..][j] == s2[j+1];
                assert s2[j+1] == (j+1) + offset;
                assert t2[j] == j + offset + 1;
            }
        }
        SumShiftLemmaGeneral(k - 1, offset + 1);
        assert sum(t1) == sum(t2) + (k-1);
        assert sum(s1) == (offset + 1) + sum(t1);
        assert sum(s2) == offset + sum(t2);
        assert sum(s1) == sum(s2) + k;
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
    /* code modified by LLM (iteration 4): use arithmetic to prove sum directly */
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
