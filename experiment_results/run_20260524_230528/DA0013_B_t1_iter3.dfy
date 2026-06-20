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
/* helper modified by LLM (iteration 3): no helpers needed */

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
  /* code modified by LLM (iteration 3): fixed witness loop and minimality proof */
  var minVal := seq_min(arr);
  var n := |arr|;
  
  // Collect all positions of minVal
  var positions: seq<int> := [];
  var idx := 0;
  while idx < n
    invariant 0 <= idx <= n
    invariant forall k :: 0 <= k < |positions| ==> 0 <= positions[k] < idx && arr[positions[k]] == minVal
    invariant forall k :: 0 <= k < idx && arr[k] == minVal ==> k in positions
    invariant |positions| == 0 || positions[|positions|-1] < idx
    invariant forall a, b :: 0 <= a < b < |positions| ==> positions[a] < positions[b]
  {
    if arr[idx] == minVal {
      positions := positions + [idx];
    }
    idx := idx + 1;
  }
  
  // positions has at least 2 elements by ValidInput
  assert |positions| >= 2;
  
  var minGap := positions[1] - positions[0];
  assert minGap > 0;
  var p := 1;
  while p < |positions| - 1
    invariant 1 <= p <= |positions| - 1
    invariant minGap > 0
    invariant exists a :: 0 <= a < p && positions[a+1] - positions[a] == minGap
    invariant forall a :: 0 <= a < p ==> positions[a+1] - positions[a] >= minGap
  {
    var gap := positions[p+1] - positions[p];
    if gap < minGap {
      minGap := gap;
    }
    p := p + 1;
  }
  
  result := minGap;
  
  // Find the witness index where gap == result
  var wi := 0;
  while wi < |positions| - 1 && positions[wi+1] - positions[wi] != result
    invariant 0 <= wi <= |positions| - 1
    invariant forall a :: 0 <= a < wi ==> positions[a+1] - positions[a] != result
  {
    wi := wi + 1;
  }
  
  // wi must be valid: since result == minGap and minGap is achieved by some consecutive pair
  assert wi < |positions| - 1;
  assert positions[wi+1] - positions[wi] == result;
  assert arr[positions[wi]] == minVal && arr[positions[wi+1]] == minVal;
  assert positions[wi] < positions[wi+1];
  
  // Prove minimality: for any i < j with arr[i] == arr[j] == minVal, j - i >= result
  assert forall i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == minVal ==> i in positions && j in positions;
}
// </vc-code>
