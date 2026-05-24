// <vc-preamble>
predicate ValidInput(n: int, a: seq<int>, p: string)
{
    n >= 2 &&
    |a| == n &&
    |p| == n - 1 &&
    (forall i :: 0 <= i < |p| ==> p[i] == '0' || p[i] == '1') &&
    (forall i :: 0 <= i < |a| ==> 1 <= a[i] <= n) &&
    (forall i :: 1 <= i <= n ==> exists j :: 0 <= j < |a| && a[j] == i)
}

function max_up_to(a: seq<int>, i: int): int
    requires 0 <= i < |a|
    decreases i
{
    if i == 0 then a[0]
    else if a[i] > max_up_to(a, i-1) then a[i]
    else max_up_to(a, i-1)
}

predicate CanSort(n: int, a: seq<int>, p: string)
    requires ValidInput(n, a, p)
{
    forall i :: 0 <= i < n - 1 ==> 
        (p[i] == '0' ==> max_up_to(a, i) <= i + 1)
}
// </vc-preamble>

// <vc-helpers>
lemma max_up_to_bound(a: seq<int>, i: int)
    requires 0 <= i < |a|
    ensures forall k :: 0 <= k <= i ==> a[k] <= max_up_to(a, i)
    decreases i
{
    if i == 0 {
    } else {
        max_up_to_bound(a, i-1);
    }
}

lemma max_up_to_is_some_element(a: seq<int>, i: int)
    requires 0 <= i < |a|
    ensures exists k :: 0 <= k <= i && a[k] == max_up_to(a, i)
    decreases i
{
    if i == 0 {
    } else {
        max_up_to_is_some_element(a, i-1);
    }
}

lemma max_up_to_monotone(a: seq<int>, i: int, j: int)
    requires 0 <= i <= j < |a|
    ensures max_up_to(a, i) <= max_up_to(a, j)
    decreases j
{
    if i == j {
    } else {
        max_up_to_monotone(a, i, j-1);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>, p: string) returns (result: string)
    requires ValidInput(n, a, p)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanSort(n, a, p)
// </vc-spec>
// <vc-code>
{
    var i := 0;
    var ok := true;
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant ok <==> forall k :: 0 <= k < i ==> (p[k] == '0' ==> max_up_to(a, k) <= k + 1)
    {
        if p[i] == '0' {
            var m := max_up_to(a, i);
            if m > i + 1 {
                ok := false;
            }
        }
        i := i + 1;
    }
    if ok {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>
