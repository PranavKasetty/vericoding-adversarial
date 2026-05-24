// <vc-preamble>
predicate ValidInput(n: int, k: int, a: seq<int>)
{
    n >= 1 && k >= 1 && |a| == n &&
    (forall i :: 0 <= i < |a| ==> a[i] >= 1) &&
    (exists i :: 0 <= i < |a| && k % a[i] == 0)
}

predicate ValidBucket(k: int, bucketSize: int)
{
    bucketSize >= 1 && k % bucketSize == 0
}

function HoursNeeded(k: int, bucketSize: int): int
    requires ValidBucket(k, bucketSize)
{
    k / bucketSize
}

predicate IsOptimalChoice(k: int, a: seq<int>, chosenBucket: int)
{
    0 <= chosenBucket < |a| &&
    ValidBucket(k, a[chosenBucket]) &&
    (forall i :: 0 <= i < |a| && ValidBucket(k, a[i]) ==> a[i] <= a[chosenBucket])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): lemma to witness that bestIdx gets set */
lemma ExistsValidBucket(k: int, a: seq<int>)
    requires |a| >= 1
    requires forall i :: 0 <= i < |a| ==> a[i] >= 1
    requires exists i :: 0 <= i < |a| && k % a[i] == 0
    ensures exists i :: 0 <= i < |a| && ValidBucket(k, a[i])
{
}

lemma BestIdxFound(k: int, a: seq<int>, n: int, bestIdx: int, loopEnd: int)
    requires n == |a|
    requires loopEnd == n
    requires exists idx :: 0 <= idx < n && ValidBucket(k, a[idx])
    requires bestIdx == -1 || (0 <= bestIdx < loopEnd && ValidBucket(k, a[bestIdx]))
    requires bestIdx == -1 || (forall j :: 0 <= j < loopEnd && ValidBucket(k, a[j]) ==> a[j] <= a[bestIdx])
    ensures bestIdx != -1
{
    if bestIdx == -1 {
        var idx :| 0 <= idx < n && ValidBucket(k, a[idx]);
        assert 0 <= idx < loopEnd;
        assert ValidBucket(k, a[idx]);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, k, a)
    ensures result >= 1
    ensures exists i :: IsOptimalChoice(k, a, i) && result == HoursNeeded(k, a[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fix loop invariant and bestIdx assertion */
  var bestIdx := -1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant i <= |a|
    invariant bestIdx == -1 || (0 <= bestIdx < i && ValidBucket(k, a[bestIdx]))
    invariant forall j :: 0 <= j < i && ValidBucket(k, a[j]) ==> (bestIdx != -1 && a[j] <= a[bestIdx])
  {
    if k % a[i] == 0 {
      if bestIdx == -1 || a[i] > a[bestIdx] {
        bestIdx := i;
      }
    }
    i := i + 1;
  }
  ExistsValidBucket(k, a);
  var witness :| 0 <= witness < |a| && ValidBucket(k, a[witness]);
  assert 0 <= witness < i;
  assert bestIdx != -1;
  assert 0 <= bestIdx < n;
  assert ValidBucket(k, a[bestIdx]);
  assert forall j :: 0 <= j < n && ValidBucket(k, a[j]) ==> a[j] <= a[bestIdx];
  assert IsOptimalChoice(k, a, bestIdx);
  result := k / a[bestIdx];
  assert result == HoursNeeded(k, a[bestIdx]);
  assert result >= 1;
}
// </vc-code>
