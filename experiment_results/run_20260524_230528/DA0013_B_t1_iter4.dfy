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
/* helper modified by LLM (iteration 4): lemma proving non-consecutive gaps >= min consecutive gap */
lemma ConsecutiveGapMinimal(positions: seq<int>, minGap: int, i: int, j: int)
    requires |positions| >= 2
    requires forall a :: 0 <= a < |positions| - 1 ==> positions[a+1] - positions[a] >= minGap
    requires forall a :: 0 <= a < |positions| - 1 ==> positions[a] < positions[a+1]
    requires 0 <= i < j < |positions|
    ensures positions[j] - positions[i] >= minGap
    decreases j - i
{
    if j == i + 1 {
        // direct consecutive gap
    } else {
        ConsecutiveGapMinimal(positions, minGap, i, j-1);
        // positions[j-1] - positions[i] >= minGap
        // positions[j] - positions[j-1] >= minGap > 0
        // so positions[j] - positions[i] >= positions[j] - positions[j-1] >= minGap
    }
}
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
  /* code modified by LLM (iteration 4): use lemma to prove non-consecutive gaps */
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
  
  assert wi < |positions| - 1;
  assert positions[wi+1] - positions[wi] == result;
  assert arr[positions[wi]] == minVal && arr[positions[wi+1]] == minVal;
  assert positions[wi] < positions[wi+1];
  
  // Prove minimality using the lemma
  forall i, j | 0 <= i < j < |arr| && arr[i] == arr[j] == minVal
    ensures j - i >= result
  {
    // i and j are in positions
    assert i in positions;
    assert j in positions;
    // Find their indices in positions
    var pi := 0;
    while pi < |positions| && positions[pi] != i
      invariant 0 <= pi <= |positions|
      invariant forall k :: 0 <= k < pi ==> positions[k] != i
    {
      pi := pi + 1;
    }
    assert pi < |positions| && positions[pi] == i;
    var pj := 0;
    while pj < |positions| && positions[pj] != j
      invariant 0 <= pj <= |positions|
      invariant forall k :: 0 <= k < pj ==> positions[k] != j
    {
      pj := pj + 1;
    }
    assert pj < |positions| && positions[pj] == j;
    assert pi < pj;
    ConsecutiveGapMinimal(positions, result, pi, pj);
  }
}
// </vc-code>
