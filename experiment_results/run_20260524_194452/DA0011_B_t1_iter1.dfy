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
lemma max_up_to_ge(a: seq<int>, i: int, j: int)
    requires 0 <= j <= i < |a|
    ensures max_up_to(a, i) >= a[j]
    decreases i
{
    if i == 0 {
        assert j == 0;
    } else if j == i {
        if a[i] > max_up_to(a, i-1) {
        } else {
        }
    } else {
        max_up_to_ge(a, i-1, j);
        if a[i] > max_up_to(a, i-1) {
        } else {
        }
    }
}

lemma max_up_to_le(a: seq<int>, i: int)
    requires 0 <= i < |a|
    ensures forall j :: 0 <= j <= i ==> max_up_to(a, i) >= a[j]
    decreases i
{
    if i == 0 {
    } else {
        max_up_to_le(a, i-1);
        if a[i] > max_up_to(a, i-1) {
        } else {
        }
    }
}

lemma max_up_to_is_some_element(a: seq<int>, i: int)
    requires 0 <= i < |a|
    ensures exists j :: 0 <= j <= i && a[j] == max_up_to(a, i)
    decreases i
{
    if i == 0 {
    } else {
        max_up_to_is_some_element(a, i-1);
        if a[i] > max_up_to(a, i-1) {
        } else {
        }
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
        invariant ok <==> (forall k :: 0 <= k < i ==> (p[k] == '0' ==> max_up_to(a, k) <= k + 1))
    {
        if p[i] == '0' {
            // compute max_up_to(a, i) iteratively
            var m := a[0];
            var j := 1;
            while j <= i
                invariant 1 <= j <= i + 1
                invariant m == max_up_to(a, j-1)
            {
                if a[j] > m {
                    m := a[j];
                }
                j := j + 1;
            }
            // now m == max_up_to(a, i)
            assert m == max_up_to(a, i);
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
