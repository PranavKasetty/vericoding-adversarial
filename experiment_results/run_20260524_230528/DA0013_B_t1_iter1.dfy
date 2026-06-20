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
  var n := |arr|;
  
  // Find first occurrence of minVal
  var firstIdx := 0;
  while firstIdx < n && arr[firstIdx] != minVal
    invariant 0 <= firstIdx <= n
    invariant forall k :: 0 <= k < firstIdx ==> arr[k] != minVal
  {
    firstIdx := firstIdx + 1;
  }
  
  // Find second occurrence of minVal after firstIdx
  var secondIdx := firstIdx + 1;
  while secondIdx < n && arr[secondIdx] != minVal
    invariant firstIdx < secondIdx <= n
    invariant arr[firstIdx] == minVal
    invariant forall k :: firstIdx < k < secondIdx ==> arr[k] != minVal
  {
    secondIdx := secondIdx + 1;
  }
  
  result := secondIdx - firstIdx;
  
  // Now prove minimality
  // For any pair (i,j) with i < j and arr[i] == arr[j] == minVal,
  // we need to show j - i >= result
  // The key insight: firstIdx is the first occurrence of minVal
  // so any i >= firstIdx, and since arr[firstIdx] == minVal and firstIdx <= i,
  // we have i == firstIdx or i > firstIdx
  // If i == firstIdx, then j >= secondIdx (since secondIdx is the next occurrence after firstIdx)
  // so j - i >= secondIdx - firstIdx = result
  // If i > firstIdx, then j > i > firstIdx, so j - i could be less...
  // Wait, we need the minimum gap, not involving firstIdx necessarily.
  // Let me reconsider: we want the minimum j-i over all pairs.
  // We need to scan all consecutive pairs of minVal occurrences.
  
  // Collect all positions of minVal and find minimum consecutive gap
  var positions: seq<int> := [];
  var idx := 0;
  while idx < n
    invariant 0 <= idx <= n
    invariant forall k :: 0 <= k < |positions| ==> 0 <= positions[k] < n && arr[positions[k]] == minVal
    invariant forall k :: 0 <= k < idx && arr[k] == minVal ==> k in positions
    invariant |positions| == 0 || (forall a, b :: 0 <= a < b < |positions| ==> positions[a] < positions[b])
  {
    if arr[idx] == minVal {
      positions := positions + [idx];
    }
    idx := idx + 1;
  }
  
  // positions has at least 2 elements by ValidInput
  var minGap := positions[1] - positions[0];
  var p := 1;
  while p < |positions| - 1
    invariant 1 <= p <= |positions| - 1
    invariant minGap > 0
    invariant exists a, b :: 0 <= a < b < |positions| && positions[b] - positions[a] == minGap
    invariant forall a, b :: 0 <= a < b <= p ==> positions[b] - positions[a] >= minGap
  {
    var gap := positions[p+1] - positions[p];
    if gap < minGap {
      minGap := gap;
    }
    p := p + 1;
  }
  
  result := minGap;
}
// </vc-code>
