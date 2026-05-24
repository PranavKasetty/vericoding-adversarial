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
  /* code modified by LLM (iteration 2): find minimum gap between any two occurrences of minimum value */
  var minVal := seq_min(arr);
  var n := |arr|;
  
  // Collect indices of minVal occurrences
  // Find first occurrence
  var firstIdx := 0;
  while firstIdx < n && arr[firstIdx] != minVal
    invariant 0 <= firstIdx <= n
    invariant forall k :: 0 <= k < firstIdx ==> arr[k] != minVal
  {
    firstIdx := firstIdx + 1;
  }
  
  // Now find the minimum gap by scanning all consecutive pairs of minVal occurrences
  // We'll track previous occurrence and minimum gap
  var prevIdx := firstIdx;
  var secondIdx := firstIdx + 1;
  while secondIdx < n && arr[secondIdx] != minVal
    invariant firstIdx + 1 <= secondIdx <= n
    invariant arr[firstIdx] == minVal
    invariant forall k :: firstIdx + 1 <= k < secondIdx ==> arr[k] != minVal
  {
    secondIdx := secondIdx + 1;
  }
  
  // secondIdx is the second occurrence
  var minGap := secondIdx - firstIdx;
  var prevOcc := firstIdx;
  var curOcc := secondIdx;
  
  // Continue scanning for closer pairs
  var idx := curOcc + 1;
  while idx < n
    invariant curOcc + 1 <= idx <= n
    invariant 0 <= prevOcc < curOcc < n
    invariant arr[prevOcc] == minVal
    invariant arr[curOcc] == minVal
    invariant minGap == curOcc - prevOcc
    invariant minGap > 0
    invariant minGap <= |arr| - 1
    invariant exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == minVal && j - i == minGap
    invariant forall i, j :: 0 <= i < j < curOcc && arr[i] == arr[j] == minVal ==> j - i >= minGap
  {
    if arr[idx] == minVal {
      if idx - curOcc < minGap {
        minGap := idx - curOcc;
      }
      prevOcc := curOcc;
      curOcc := idx;
    }
    idx := idx + 1;
  }
  
  result := minGap;
}
// </vc-code>
