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
/* helper modified by LLM (iteration 3): fix SumOfRange by proving sequence equality explicitly */
lemma SeqTailShift(k: int, offset: int, extra: int)
    requires k >= 1
    ensures seq(k, i => if i < k - 1 then i + offset else i + offset + extra)[1..] == seq(k - 1, i => if i < k - 2 then i + (offset + 1) else i + (offset + 1) + extra)
{
    var s := seq(k, i => if i < k - 1 then i + offset else i + offset + extra);
    var t := seq(k - 1, i => if i < k - 2 then i + (offset + 1) else i + (offset + 1) + extra);
    assert |s[1..]| == k - 1;
    assert |t| == k - 1;
    forall j | 0 <= j < k - 1
        ensures s[1..][j] == t[j]
    {
        assert s[1..][j] == s[j + 1];
    }
}

lemma SumOfFirstKMinus1ThenLastShifted2(k: int, extra: int, offset: int)
    requires k >= 1
    requires extra >= 0
    requires offset >= 1
    ensures sum(seq(k, i => if i < k - 1 then i + offset else i + offset + extra)) == k * (2 * offset + k - 1) / 2 + extra
    decreases k
{
    if k == 1 {
        var s := seq(1, i => if i < 0 then i + offset else i + offset + extra);
        assert s == [offset + extra];
    } else {
        var s := seq(k, i => if i < k - 1 then i + offset else i + offset + extra);
        assert s[0] == offset;
        SeqTailShift(k, offset, extra);
        SumOfFirstKMinus1ThenLastShifted2(k - 1, extra, offset + 1);
    }
}

lemma SeqAllSame(k: int)
    requires k >= 1
    ensures seq(k, i => if i < k - 1 then i + 1 else i + 1 + 0) == seq(k, i => i + 1)
{
    var s := seq(k, i => if i < k - 1 then i + 1 else i + 1 + 0);
    var t := seq(k, i => i + 1);
    assert |s| == |t|;
    forall j | 0 <= j < k
        ensures s[j] == t[j]
    {
        if j < k - 1 {
            assert s[j] == j + 1;
            assert t[j] == j + 1;
        } else {
            assert s[j] == j + 1 + 0;
            assert t[j] == j + 1;
        }
    }
    assert s == t;
}

lemma SumOfRange(k: int)
    requires k >= 1
    ensures sum(seq(k, i => i + 1)) == k * (k + 1) / 2
    decreases k
{
    SeqAllSame(k);
    SumOfFirstKMinus1ThenLastShifted2(k, 0, 1);
    assert sum(seq(k, i => if i < k - 1 then i + 1 else i + 1 + 0)) == k * (k + 1) / 2;
}

lemma SumOfFirstKMinus1ThenLast(k: int, extra: int)
    requires k >= 1
    requires extra >= 0
    ensures sum(seq(k, i => if i < k - 1 then i + 1 else i + 1 + extra)) == k * (k + 1) / 2 + extra
{
    SumOfFirstKMinus1ThenLastShifted2(k, extra, 1);
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
    /* code modified by LLM (iteration 3): use fixed helper lemmas */
    if k * (k + 1) / 2 > n {
        result := [-1];
    } else {
        var extra := n - k * (k + 1) / 2;
        result := seq(k, i => if i < k - 1 then i + 1 else i + 1 + extra);
        assert forall i :: 0 <= i < |result| ==> result[i] > 0 by {
            forall i | 0 <= i < |result|
                ensures result[i] > 0
            {
                if i < k - 1 {
                    assert result[i] == i + 1;
                } else {
                    assert result[i] == k + extra;
                    assert extra >= 0;
                }
            }
        }
        assert forall i :: 0 <= i < |result| - 1 ==> result[i] < result[i+1] by {
            forall i | 0 <= i < |result| - 1
                ensures result[i] < result[i+1]
            {
                if i < k - 2 {
                    assert result[i] == i + 1;
                    assert result[i+1] == i + 2;
                } else {
                    assert i == k - 2;
                    assert result[i] == k - 1;
                    assert result[i+1] == k + extra;
                    assert extra >= 0;
                }
            }
        }
        SumOfFirstKMinus1ThenLast(k, extra);
        assert sum(result) == n;
    }
}
// </vc-code>
