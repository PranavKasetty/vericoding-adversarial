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
// Helper lemmas for the solve method
lemma SumOfRange(k: int)
    requires k >= 1
    ensures sum(seq(k, i => i + 1)) == k * (k + 1) / 2
    decreases k
{
    if k == 1 {
        assert seq(1, i => i + 1) == [1];
    } else {
        var s := seq(k, i => i + 1);
        var s' := seq(k - 1, i => i + 1);
        assert s[0] == 1;
        assert s[1..] == seq(k - 1, i => i + 2);
        SumOfRange(k - 1);
        ShiftedSumEquals(k - 1);
    }
}

lemma ShiftedSumEquals(k: int)
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
        ShiftedSumEquals(k - 1);
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
    if k * (k + 1) / 2 > n {
        result := [-1];
    } else {
        var extra := n - k * (k + 1) / 2;
        // Build sequence [1, 2, 3, ..., k-1, k + extra]
        result := seq(k, i => if i < k - 1 then i + 1 else i + 1 + extra);
        // Prove AllPositive
        assert forall i :: 0 <= i < |result| ==> result[i] > 0 by {
            forall i | 0 <= i < |result| {
                if i < k - 1 {
                    assert result[i] == i + 1;
                } else {
                    assert result[i] == k + extra;
                    assert extra >= 0;
                }
            }
        }
        // Prove IsStrictlyIncreasing
        assert forall i :: 0 <= i < |result| - 1 ==> result[i] < result[i+1] by {
            forall i | 0 <= i < |result| - 1 {
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
        // Prove sum == n
        assert sum(result) == n by {
            var s := result;
            assert |s| == k;
            // sum of [1..k-1, k+extra] = (k-1)*k/2 + k + extra = k*(k+1)/2 + extra = n
            SumOfFirstKMinus1ThenLast(k, extra);
        }
    }
}

lemma SumOfFirstKMinus1ThenLast(k: int, extra: int)
    requires k >= 1
    requires extra >= 0
    ensures sum(seq(k, i => if i < k - 1 then i + 1 else i + 1 + extra)) == k * (k + 1) / 2 + extra
    decreases k
{
    if k == 1 {
        var s := seq(1, i => if i < 0 then i + 1 else i + 1 + extra);
        assert s == [1 + extra];
        assert sum(s) == 1 + extra;
    } else {
        var s := seq(k, i => if i < k - 1 then i + 1 else i + 1 + extra);
        assert s[0] == 1;
        assert s[1..] == seq(k - 1, i => if i < k - 2 then i + 2 else i + 2 + extra);
        SumOfFirstKMinus1ThenLastShifted(k - 1, extra);
    }
}

lemma SumOfFirstKMinus1ThenLastShifted(k: int, extra: int)
    requires k >= 1
    requires extra >= 0
    ensures sum(seq(k, i => if i < k - 1 then i + 2 else i + 2 + extra)) == k * (k + 1) / 2 + k + extra
    decreases k
{
    if k == 1 {
        var s := seq(1, i => if i < 0 then i + 2 else i + 2 + extra);
        assert s == [2 + extra];
    } else {
        var s := seq(k, i => if i < k - 1 then i + 2 else i + 2 + extra);
        assert s[0] == 2;
        assert s[1..] == seq(k - 1, i => if i < k - 2 then i + 3 else i + 3 + extra);
        SumOfFirstKMinus1ThenLastShifted2(k - 1, extra, 3);
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
        assert s[1..] == seq(k - 1, i => if i < k - 2 then i + offset + 1 else i + offset + 1 + extra);
        SumOfFirstKMinus1ThenLastShifted2(k - 1, extra, offset + 1);
    }
}
// </vc-code>
