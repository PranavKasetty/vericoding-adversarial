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
  var remA := a;
  var remB := b;
  var halfOccupied := 0;
  var i := 0;

  // We need to show that our iterative computation matches the recursive definition
  // We'll use a ghost variable to track the recursive state
  
  while i < n
    invariant 0 <= i <= n
    invariant remA >= 0 && remB >= 0 && halfOccupied >= 0
    invariant denied >= 0
    invariant denied + countDeniedPeopleWithHalf(groups[i..], remA, remB, halfOccupied) == countDeniedPeopleWithHalf(groups, a, b, 0)
  {
    var group := groups[i];
    if group == 2 {
      if remB > 0 {
        remB := remB - 1;
      } else {
        denied := denied + 2;
      }
    } else {
      if remA > 0 {
        remA := remA - 1;
      } else if remB > 0 {
        remB := remB - 1;
        halfOccupied := halfOccupied + 1;
      } else if halfOccupied > 0 {
        halfOccupied := halfOccupied - 1;
      } else {
        denied := denied + 1;
      }
    }
    i := i + 1;
  }

  assert groups[n..] == [];
}
// </vc-code>
