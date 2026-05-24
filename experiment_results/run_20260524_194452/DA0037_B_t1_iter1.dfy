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

// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, k, a)
    ensures result >= 1
    ensures exists i :: IsOptimalChoice(k, a, i) && result == HoursNeeded(k, a[i])
// </vc-spec>
// <vc-code>
{
  var bestBucket := -1;
  var bestIdx := -1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant bestIdx == -1 || (0 <= bestIdx < i && ValidBucket(k, a[bestIdx]))
    invariant bestIdx == -1 || bestBucket == a[bestIdx]
    invariant bestIdx == -1 ==> (forall j :: 0 <= j < i ==> !ValidBucket(k, a[j]))
    invariant bestIdx != -1 ==> (forall j :: 0 <= j < i && ValidBucket(k, a[j]) ==> a[j] <= bestBucket)
  {
    if k % a[i] == 0 {
      if bestIdx == -1 || a[i] > bestBucket {
        bestBucket := a[i];
        bestIdx := i;
      }
    }
    i := i + 1;
  }
  result := k / bestBucket;
}
// </vc-code>
