// <vc-preamble>
function seq_min(s: seq<int>): int
    requires |s| > 0
    ensures seq_min(s) in s
    ensures forall k :: 0 <= k < |s| ==> seq_min(s) <= s[k]
{
    if |s| == 1 then s[0]
    else if s[0] <= seq_min(s[1..]) then s[0]
    else seq_min(s[1..])
}

predicate ValidInput(arr: seq<int>)
{
    |arr| >= 2 && 
    exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(arr: seq<int>) returns (result: int)
    requires ValidInput(arr)
    ensures result > 0
    ensures result <= |arr| - 1
    ensures exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr) && j - i == result
    ensures forall i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr) ==> j - i >= result
// </vc-spec>
// <vc-code>
{
  var minVal := seq_min(arr);
  var firstIdx := -1;
  var secondIdx := -1;
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant firstIdx == -1 ==> forall k :: 0 <= k < i ==> arr[k] != minVal
    invariant firstIdx != -1 ==> 0 <= firstIdx < i && arr[firstIdx] == minVal
    invariant firstIdx != -1 ==> forall k :: 0 <= k < firstIdx ==> arr[k] != minVal
    invariant secondIdx == -1 ==> (firstIdx == -1 || forall k :: firstIdx < k < i ==> arr[k] != minVal)
    invariant secondIdx != -1 ==> firstIdx != -1 && firstIdx < secondIdx < i && arr[secondIdx] == minVal
    invariant secondIdx != -1 ==> forall k :: firstIdx < k < secondIdx ==> arr[k] != minVal
  {
    if arr[i] == minVal {
      if firstIdx == -1 {
        firstIdx := i;
      } else if secondIdx == -1 {
        secondIdx := i;
      }
    }
    i := i + 1;
  }
  assert firstIdx != -1;
  assert secondIdx != -1;
  result := secondIdx - firstIdx;
  // Now prove this is minimal
  // We need to show that for any i,j with arr[i]==arr[j]==minVal and 0<=i<j<|arr|, j-i >= result
  // Since firstIdx is the first occurrence and secondIdx is the second consecutive occurrence after firstIdx,
  // any pair (i,j) must have i >= firstIdx (since firstIdx is first), so j >= secondIdx,
  // meaning j - i >= secondIdx - firstIdx = result
  // Wait, that's not quite right. Let's think again.
  // firstIdx is the first index where arr[k]==minVal.
  // secondIdx is the second index where arr[k]==minVal (the one right after firstIdx with no minVal in between).
  // For any pair (p,q) with p<q and arr[p]==arr[q]==minVal:
  //   p >= firstIdx (since firstIdx is first occurrence)
  //   if p == firstIdx, then q >= secondIdx, so q-p >= secondIdx-firstIdx = result
  //   if p > firstIdx, then there exists some occurrence between firstIdx and p (namely secondIdx <= p),
  //     but then secondIdx <= p < q, so q > p >= secondIdx > firstIdx
  //     and q - p could be anything... hmm
  // Actually we want the minimum gap, not first two occurrences.
  // Let me redo this with a proper search.
  // Reset and search for minimum gap
  var minGap := |arr|;
  var lastMinIdx := -1;
  var j := 0;
  while j < |arr|
    invariant 0 <= j <= |arr|
    invariant lastMinIdx == -1 ==> forall k :: 0 <= k < j ==> arr[k] != minVal
    invariant lastMinIdx != -1 ==> 0 <= lastMinIdx < j && arr[lastMinIdx] == minVal
    invariant lastMinIdx != -1 ==> forall k :: lastMinIdx < k < j ==> arr[k] != minVal
    invariant minGap <= |arr|
    invariant minGap > 0
    invariant lastMinIdx == -1 ==> minGap == |arr|
    invariant lastMinIdx != -1 && minGap < |arr| ==> exists p, q :: 0 <= p < q < |arr| && arr[p] == arr[q] == minVal && q - p == minGap
    invariant forall p, q :: 0 <= p < q < j && arr[p] == arr[q] == minVal ==> q - p >= minGap
  {
    if arr[j] == minVal {
      if lastMinIdx != -1 {
        var gap := j - lastMinIdx;
        if gap < minGap {
          minGap := gap;
        }
      }
      lastMinIdx := j;
    }
    j := j + 1;
  }
  result := minGap;
}
// </vc-code>
