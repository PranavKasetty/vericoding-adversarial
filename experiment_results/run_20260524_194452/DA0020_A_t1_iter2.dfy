// <vc-preamble>
predicate ValidInput(n: nat, arr: seq<int>)
{
    n > 0 && |arr| == n && forall i :: 0 <= i < |arr| ==> arr[i] >= 1
}

predicate IsUnimodal(arr: seq<int>)
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
{
    if |arr| <= 1 then true
    else
        var phases := ComputePhases(arr);
        phases.0 <= phases.1 <= phases.2 == |arr| &&
        (forall i, j :: 0 <= i < j < phases.0 ==> arr[i] < arr[j]) &&
        (forall i :: phases.0 <= i < phases.1 ==> arr[i] == (if phases.0 > 0 then arr[phases.0] else arr[0])) &&
        (forall i, j :: phases.1 <= i < j < phases.2 ==> arr[i] > arr[j]) &&
        (phases.0 > 0 && phases.1 < |arr| ==> arr[phases.0-1] >= (if phases.1 > phases.0 then arr[phases.0] else arr[phases.1]))
}

function ComputePhases(arr: seq<int>): (int, int, int)
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    ensures var (incEnd, constEnd, decEnd) := ComputePhases(arr); 0 <= incEnd <= constEnd <= decEnd <= |arr|
{
    var incEnd := ComputeIncreasingEnd(arr, 0, 0);
    var constEnd := ComputeConstantEnd(arr, incEnd, if incEnd > 0 then arr[incEnd-1] else 0);
    var decEnd := ComputeDecreasingEnd(arr, constEnd, if constEnd > incEnd then arr[incEnd] else if incEnd > 0 then arr[incEnd-1] else 0);
    (incEnd, constEnd, decEnd)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simplified helpers, removed CheckUnimodalImperative, kept basic phase helpers */
function ComputeIncreasingEnd(arr: seq<int>, i: int, acc: int): int
    requires forall k :: 0 <= k < |arr| ==> arr[k] >= 1
    requires 0 <= i <= |arr|
    requires 0 <= acc <= i
    ensures var r := ComputeIncreasingEnd(arr, i, acc); 0 <= r <= |arr|
    decreases |arr| - i
{
    if i >= |arr| - 1 then
        if i == 0 then 0
        else if i < |arr| && acc == i then i
        else acc
    else if arr[i] < arr[i+1] then
        ComputeIncreasingEnd(arr, i+1, i+1)
    else
        acc
}

function ComputeConstantEnd(arr: seq<int>, start: int, val: int): int
    requires forall k :: 0 <= k < |arr| ==> arr[k] >= 1
    requires 0 <= start <= |arr|
    ensures var r := ComputeConstantEnd(arr, start, val); start <= r <= |arr|
    decreases |arr| - start
{
    if start >= |arr| then start
    else if val == 0 then start
    else if arr[start] == val then
        ComputeConstantEnd(arr, start+1, val)
    else
        start
}

function ComputeDecreasingEnd(arr: seq<int>, start: int, val: int): int
    requires forall k :: 0 <= k < |arr| ==> arr[k] >= 1
    requires 0 <= start <= |arr|
    ensures var r := ComputeDecreasingEnd(arr, start, val); start <= r <= |arr|
    decreases |arr| - start
{
    if start >= |arr| - 1 then |arr|
    else if val == 0 then |arr|
    else if arr[start] > arr[start+1] then
        ComputeDecreasingEnd(arr, start+1, arr[start+1])
    else if arr[start] == arr[start+1] then
        start
    else
        start
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, arr: seq<int>) returns (result: string)
    requires ValidInput(n, arr)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> IsUnimodal(arr)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use ComputePhases directly and check IsUnimodal conditions */
    var phases := ComputePhases(arr);
    var incEnd := phases.0;
    var constEnd := phases.1;
    var decEnd := phases.2;
    var isUnimodal := IsUnimodal(arr);
    if isUnimodal {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>
