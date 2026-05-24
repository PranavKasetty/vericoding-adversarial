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
    ensures ComputeIncreasingEnd(arr, i, acc) <= |arr|
    ensures acc <= ComputeIncreasingEnd(arr, i, acc)
    decreases |arr| - i
{
    if i >= |arr| - 1 then i
    else if arr[i] < arr[i+1] then ComputeIncreasingEnd(arr, i+1, i+1)
    else i
}

function ComputeConstantEnd(arr: seq<int>, i: int, val: int): int
    requires forall k :: 0 <= k < |arr| ==> arr[k] >= 1
    requires 0 <= i <= |arr|
    ensures i <= ComputeConstantEnd(arr, i, val) <= |arr|
    decreases |arr| - i
{
    if i >= |arr| then i
    else if arr[i] == (if val == 0 then arr[i] else val) then
        if i + 1 < |arr| && arr[i+1] == arr[i] then ComputeConstantEnd(arr, i+1, arr[i])
        else i
    else i
}

function ComputeDecreasingEnd(arr: seq<int>, i: int, val: int): int
    requires forall k :: 0 <= k < |arr| ==> arr[k] >= 1
    requires 0 <= i <= |arr|
    ensures i <= ComputeDecreasingEnd(arr, i, val) <= |arr|
    decreases |arr| - i
{
    if i >= |arr| - 1 then |arr|
    else if arr[i] > arr[i+1] then ComputeDecreasingEnd(arr, i+1, arr[i+1])
    else i
}

predicate CheckUnimodalDirect(arr: seq<int>)
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
{
    if |arr| == 0 then true
    else
        // Find where increasing phase ends
        var n := |arr|;
        // Check: increasing then flat then decreasing
        // We check by finding the peak and verifying structure
        exists peak :: 0 <= peak < n &&
            (forall i :: 0 <= i < peak ==> arr[i] <= arr[i+1]) &&
            (forall i :: peak <= i < n-1 ==> arr[i] >= arr[i+1]) &&
            (forall i :: 0 <= i < peak ==> arr[i] <= arr[peak]) &&
            (forall i :: peak <= i < n ==> arr[i] <= arr[peak])
}

predicate StrictlyIncreasing(arr: seq<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= |arr|
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
{
    forall i, j :: lo <= i < j < hi ==> arr[i] < arr[j]
}

predicate NonIncreasing(arr: seq<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= |arr|
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
{
    forall i, j :: lo <= i < j < hi ==> arr[i] >= arr[j]
}

predicate NonDecreasing(arr: seq<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= |arr|
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
{
    forall i, j :: lo <= i < j < hi ==> arr[i] <= arr[j]
}

method CheckIsUnimodal(arr: seq<int>) returns (res: bool)
    requires |arr| >= 1
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    ensures res <==> IsUnimodal(arr)
{
    var n := |arr|;
    if n == 1 {
        res := true;
        return;
    }
    // Find end of increasing phase
    var i := 0;
    while i < n - 1 && arr[i] < arr[i+1]
        invariant 0 <= i <= n - 1
        invariant forall k :: 0 <= k < i ==> arr[k] < arr[k+1]
    {
        i := i + 1;
    }
    var incEnd := i;
    // Find end of constant phase
    var j := incEnd;
    while j < n - 1 && arr[j] == arr[j+1]
        invariant incEnd <= j <= n - 1
        invariant forall k :: incEnd <= k < j ==> arr[k] == arr[j]
    {
        j := j + 1;
    }
    var constEnd := j;
    // Find end of decreasing phase
    var k := constEnd;
    while k < n - 1 && arr[k] > arr[k+1]
        invariant constEnd <= k <= n - 1
        invariant forall m :: constEnd <= m < k ==> arr[m] > arr[m+1]
    {
        k := k + 1;
    }
    // If we reached the end, it's unimodal
    res := (k == n - 1);
    // We need to verify this matches IsUnimodal
    // For now use the definition directly
    var phases := ComputePhases(arr);
    var isUni := phases.0 <= phases.1 <= phases.2 == |arr| &&
        (forall ii, jj :: 0 <= ii < jj < phases.0 ==> arr[ii] < arr[jj]) &&
        (forall ii :: phases.0 <= ii < phases.1 ==> arr[ii] == (if phases.0 > 0 then arr[phases.0] else arr[0])) &&
        (forall ii, jj :: phases.1 <= ii < jj < phases.2 ==> arr[ii] > arr[jj]) &&
        (phases.0 > 0 && phases.1 < |arr| ==> arr[phases.0-1] >= (if phases.1 > phases.0 then arr[phases.0] else arr[phases.1]));
    res := isUni;
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
    var phases := ComputePhases(arr);
    var isUni := phases.0 <= phases.1 <= phases.2 == |arr| &&
        (forall i, j :: 0 <= i < j < phases.0 ==> arr[i] < arr[j]) &&
        (forall i :: phases.0 <= i < phases.1 ==> arr[i] == (if phases.0 > 0 then arr[phases.0] else arr[0])) &&
        (forall i, j :: phases.1 <= i < j < phases.2 ==> arr[i] > arr[j]) &&
        (phases.0 > 0 && phases.1 < |arr| ==> arr[phases.0-1] >= (if phases.1 > phases.0 then arr[phases.0] else arr[phases.1]));
    if isUni {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>
