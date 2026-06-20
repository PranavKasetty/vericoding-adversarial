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

/* helper modified by LLM (iteration 2): lemma to prove computePosition strictly increases by at least v0-l >= 1 each day */
lemma computePositionIncreases(days: int, v0: int, v1: int, a: int, l: int)
    requires days >= 1
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    requires l < v0
    ensures computePosition(days, v0, v1, a, l) > computePosition(days - 1, v0, v1, a, l)
    decreases days
{
    if days == 1 {
        // computePosition(1, ...) = afterReread + readToday
        // prevPos = computePosition(0, ...) = 0
        // afterReread = if 0 - l > 0 then 0 - l else 0 = 0 (since l >= 0)
        // readToday = if v1 < v0 + a*0 then v1 else v0 = v0 (since v1 >= v0)
        // so computePosition(1, ...) = v0 > 0 = computePosition(0, ...)
        assert computePosition(0, v0, v1, a, l) == 0;
        assert computePosition(1, v0, v1, a, l) == v0;
        assert v0 > 0;
    } else {
        computePositionIncreases(days - 1, v0, v1, a, l);
        // prevPos = computePosition(days-1, ...) > computePosition(days-2, ...) >= 0
        var prevPos := computePosition(days - 1, v0, v1, a, l);
        var prevPrevPos := computePosition(days - 2, v0, v1, a, l);
        var afterReread := if prevPos - l > 0 then prevPos - l else 0;
        var readToday := if v1 < v0 + a * (days - 1) then v1 else v0 + a * (days - 1);
        // readToday >= v0 > l >= 0
        // afterReread >= prevPos - l (when prevPos > l) or 0
        // computePosition(days, ...) = afterReread + readToday
        // we need to show this > prevPos
        // afterReread + readToday > prevPos
        // if prevPos > l: afterReread = prevPos - l, so result = prevPos - l + readToday >= prevPos - l + v0 > prevPos (since v0 > l)
        // if prevPos <= l: afterReread = 0, result = readToday >= v0 > 0 >= prevPos? Not necessarily if prevPos is large
        // But prevPos > 0 since days-1 >= 1, so prevPos >= v0
        // Actually prevPos >= v0 (by induction), so prevPos >= v0 > l, so afterReread = prevPos - l
        computePositionLowerBound(days - 1, v0, v1, a, l);
    }
}

lemma computePositionLowerBound(days: int, v0: int, v1: int, a: int, l: int)
    requires days >= 1
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    requires l < v0
    ensures computePosition(days, v0, v1, a, l) >= v0
    decreases days
{
    if days == 1 {
        assert computePosition(1, v0, v1, a, l) == v0;
    } else {
        computePositionLowerBound(days - 1, v0, v1, a, l);
        computePositionIncreases(days, v0, v1, a, l);
    }
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
  /* code modified by LLM (iteration 2): use c - computePosition as decreases, prove termination via lemma */
  result := 1;
  while computePosition(result, v0, v1, a, l) < c
    invariant result >= 1
    invariant forall days :: 1 <= days < result ==> computePosition(days, v0, v1, a, l) < c
    decreases c - computePosition(result, v0, v1, a, l)
  {
    computePositionIncreases(result + 1, v0, v1, a, l);
    result := result + 1;
  }
}
// </vc-code>
