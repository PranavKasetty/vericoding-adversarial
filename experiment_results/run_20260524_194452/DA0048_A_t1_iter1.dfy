// <vc-preamble>
predicate ValidInput(n: int, a: int, b: int, groups: seq<int>)
{
    n >= 1 && a >= 1 && b >= 1 && |groups| == n &&
    forall i :: 0 <= i < |groups| ==> groups[i] == 1 || groups[i] == 2
}

function countDeniedPeople(groups: seq<int>, a: int, b: int): int
    requires a >= 0 && b >= 0
    requires forall i :: 0 <= i < |groups| ==> groups[i] == 1 || groups[i] == 2
    decreases |groups|
{
    countDeniedPeopleWithHalf(groups, a, b, 0)
}

function countDeniedPeopleWithHalf(groups: seq<int>, a: int, b: int, halfOccupied: int): int
    requires a >= 0 && b >= 0 && halfOccupied >= 0
    requires forall i :: 0 <= i < |groups| ==> groups[i] == 1 || groups[i] == 2
    decreases |groups|
{
    if |groups| == 0 then 0
    else
        var group := groups[0];
        var rest := groups[1..];
        if group == 2 then
            if b > 0 then countDeniedPeopleWithHalf(rest, a, b - 1, halfOccupied)
            else 2 + countDeniedPeopleWithHalf(rest, a, b, halfOccupied)
        else
            if a > 0 then countDeniedPeopleWithHalf(rest, a - 1, b, halfOccupied)
            else if b > 0 then countDeniedPeopleWithHalf(rest, a, b - 1, halfOccupied + 1)
            else if halfOccupied > 0 then countDeniedPeopleWithHalf(rest, a, b, halfOccupied - 1)
            else 1 + countDeniedPeopleWithHalf(rest, a, b, halfOccupied)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, groups: seq<int>) returns (denied: int)
    requires ValidInput(n, a, b, groups)
    ensures denied >= 0
    ensures denied == countDeniedPeople(groups, a, b)
// </vc-spec>
// <vc-code>
{
  denied := 0;
  var halfOccupied := 0;
  var aRemain := a;
  var bRemain := b;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant aRemain >= 0 && bRemain >= 0 && halfOccupied >= 0
    invariant denied >= 0
    invariant denied + countDeniedPeopleWithHalf(groups[i..], aRemain, bRemain, halfOccupied) == countDeniedPeople(groups, a, b)
  {
    var group := groups[i];
    if group == 2 {
      if bRemain > 0 {
        bRemain := bRemain - 1;
      } else {
        denied := denied + 2;
      }
    } else {
      if aRemain > 0 {
        aRemain := aRemain - 1;
      } else if bRemain > 0 {
        bRemain := bRemain - 1;
        halfOccupied := halfOccupied + 1;
      } else if halfOccupied > 0 {
        halfOccupied := halfOccupied - 1;
      } else {
        denied := denied + 1;
      }
    }
    i := i + 1;
  }
}
// </vc-code>
