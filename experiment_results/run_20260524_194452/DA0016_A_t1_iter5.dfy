// <vc-preamble>
function computePosition(days: int, v0: int, v1: int, a: int, l: int): int
    requires days >= 0
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    decreases days
{
    if days == 0 then 0
    else
        var prevPos := computePosition(days - 1, v0, v1, a, l);
        var afterReread := if prevPos - l > 0 then prevPos - l else 0;
        var readToday := if v1 < v0 + a * (days - 1) then v1 else v0 + a * (days - 1);
        afterReread + readToday
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma showing computePosition grows by at least (v0-l) per step and reaches c within c steps */
lemma computePositionGrowth(days: int, v0: int, v1: int, a: int, l: int)
    requires days >= 0
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    requires v0 > l
    ensures computePosition(days, v0, v1, a, l) >= days * (v0 - l)
{
    if days == 0 {
    } else {
        computePositionGrowth(days - 1, v0, v1, a, l);
        var prevPos := computePosition(days - 1, v0, v1, a, l);
        var afterReread := if prevPos - l > 0 then prevPos - l else 0;
        var readToday := if v1 < v0 + a * (days - 1) then v1 else v0 + a * (days - 1);
        assert afterReread >= prevPos - l;
        assert readToday >= v0;
        assert computePosition(days, v0, v1, a, l) == afterReread + readToday;
        assert afterReread + readToday >= (prevPos - l) + v0;
        assert prevPos >= (days - 1) * (v0 - l);
    }
}

lemma computePositionUpperBound(c: int, v0: int, v1: int, a: int, l: int)
    requires c >= 1
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    requires v0 > l
    ensures computePosition(c, v0, v1, a, l) >= c
{
    computePositionGrowth(c, v0, v1, a, l);
    // c * (v0 - l) >= c requires v0 - l >= 1, i.e., v0 > l
    // We need to prove c * (v0 - l) >= c
    // Since v0 > l, v0 - l >= 1, so c * (v0 - l) >= c * 1 = c
    var diff := v0 - l;
    assert diff >= 1;
    assert c * diff >= c * 1 == c;
}
// </vc-helpers>

// <vc-spec>
method solve(c: int, v0: int, v1: int, a: int, l: int) returns (result: int)
    requires 1 <= c <= 1000
    requires 0 <= l < v0 <= v1 <= 1000
    requires 0 <= a <= 1000
    ensures result >= 1
    ensures computePosition(result, v0, v1, a, l) >= c
    ensures forall days :: 1 <= days < result ==> computePosition(days, v0, v1, a, l) < c
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): use upper bound lemma, loop with explicit bound */
  computePositionUpperBound(c, v0, v1, a, l);
  result := 1;
  while computePosition(result, v0, v1, a, l) < c
    invariant result >= 1
    invariant result <= c
    invariant forall days :: 1 <= days < result ==> computePosition(days, v0, v1, a, l) < c
    decreases c - result
  {
    result := result + 1;
  }
}
// </vc-code>
