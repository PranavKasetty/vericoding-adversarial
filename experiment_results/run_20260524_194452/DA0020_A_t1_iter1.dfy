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

predicate CheckUnimodalDirect(arr: seq<int>)
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
{
    if |arr| <= 1 then true
    else
        exists peak :: 0 <= peak < |arr| &&
        (forall i, j :: 0 <= i < j <= peak ==> arr[i] <= arr[j]) &&
        (forall i, j :: peak <= i < j < |arr| ==> arr[i] >= arr[j]) &&
        (forall i :: 0 < i <= peak ==> arr[i-1] < arr[i] || arr[i-1] == arr[i]) &&
        (forall i :: peak <= i < |arr| - 1 ==> arr[i] > arr[i+1] || arr[i] == arr[i+1])
}

method CheckUnimodalImperative(arr: seq<int>) returns (result: bool)
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    ensures result <==> CheckUnimodalSimple(arr)
{
    if |arr| <= 1 {
        return true;
    }
    var i := 0;
    // increasing phase
    while i < |arr| - 1 && arr[i] < arr[i+1]
        invariant 0 <= i <= |arr|
    {
        i := i + 1;
    }
    // constant phase
    while i < |arr| - 1 && arr[i] == arr[i+1]
        invariant 0 <= i <= |arr|
    {
        i := i + 1;
    }
    // decreasing phase
    while i < |arr| - 1 && arr[i] > arr[i+1]
        invariant 0 <= i <= |arr|
    {
        i := i + 1;
    }
    result := (i == |arr| - 1);
}

predicate CheckUnimodalSimple(arr: seq<int>)
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
{
    if |arr| <= 1 then true
    else
        var n := |arr|;
        var i := FindPhaseEnd(arr, 0, Phase.Inc);
        var j := FindPhaseEnd(arr, i, Phase.Const);
        var k := FindPhaseEnd(arr, j, Phase.Dec);
        k == n
}

datatype Phase = Inc | Const | Dec

function FindPhaseEnd(arr: seq<int>, start: int, phase: Phase): int
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    requires 0 <= start <= |arr|
    ensures start <= FindPhaseEnd(arr, start, phase) <= |arr|
    decreases |arr| - start
{
    if start >= |arr| - 1 then
        if start < |arr| then |arr| - 0
        else start
    else
        match phase {
            case Inc =>
                if arr[start] < arr[start+1] then FindPhaseEnd(arr, start+1, Inc)
                else start
            case Const =>
                if arr[start] == arr[start+1] then FindPhaseEnd(arr, start+1, Const)
                else start
            case Dec =>
                if arr[start] > arr[start+1] then FindPhaseEnd(arr, start+1, Dec)
                else start
        }
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
    if |arr| <= 1 {
        return "YES";
    }
    var i := 0;
    var sz := |arr|;
    // Increasing phase
    while i < sz - 1 && arr[i] < arr[i+1]
        invariant 0 <= i <= sz
    {
        i := i + 1;
    }
    // Constant phase
    while i < sz - 1 && arr[i] == arr[i+1]
        invariant 0 <= i <= sz
    {
        i := i + 1;
    }
    // Decreasing phase
    while i < sz - 1 && arr[i] > arr[i+1]
        invariant 0 <= i <= sz
    {
        i := i + 1;
    }
    if i == sz - 1 {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>
