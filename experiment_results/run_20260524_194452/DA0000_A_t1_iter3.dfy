// <vc-preamble>
function intToDigits(x: int): seq<int>
  requires x >= 0
{
  if x == 0 then [0]
  else intToDigitsHelper(x)
}

function intToDigitsHelper(x: int): seq<int>
  requires x > 0
  decreases x
{
  if x < 10 then [x]
  else intToDigitsHelper(x / 10) + [x % 10]
}

function digitSum(digits: seq<int>): int
{
  if |digits| == 0 then 0
  else digits[0] + digitSum(digits[1..])
}

predicate ValidInput(x: int)
{
  x >= 1
}

predicate ValidResult(x: int, result: int)
  requires ValidInput(x)
{
  result > 0 &&
  result <= x &&
  (forall y :: 1 <= y <= x ==> digitSum(intToDigits(y)) <= digitSum(intToDigits(result))) &&
  (forall y :: 1 <= y <= x && digitSum(intToDigits(y)) == digitSum(intToDigits(result)) ==> y <= result)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): use ghost var to track witness explicitly */
lemma digitSumExists(x: int)
  requires x >= 1
  ensures exists y :: 1 <= y <= x && forall z :: 1 <= z <= x ==> digitSum(intToDigits(z)) <= digitSum(intToDigits(y))
{
  var i := 2;
  var best := 1;
  while i <= x
    invariant 2 <= i <= x + 1
    invariant 1 <= best < i
    invariant best <= x
    invariant forall z :: 1 <= z < i ==> digitSum(intToDigits(z)) <= digitSum(intToDigits(best))
  {
    if digitSum(intToDigits(i)) > digitSum(intToDigits(best)) {
      best := i;
    }
    i := i + 1;
  }
  assert forall z :: 1 <= z <= x ==> digitSum(intToDigits(z)) <= digitSum(intToDigits(best));
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
  requires ValidInput(x)
  ensures ValidResult(x, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): start loop at 2 to fix best < i invariant */
  var i := 2;
  var best := 1;
  var bestSum := digitSum(intToDigits(1));
  while i <= x
    invariant 2 <= i <= x + 1
    invariant 1 <= best < i
    invariant best <= x
    invariant bestSum == digitSum(intToDigits(best))
    invariant forall z :: 1 <= z < i ==> digitSum(intToDigits(z)) <= bestSum
    invariant forall z :: 1 <= z < i && digitSum(intToDigits(z)) == bestSum ==> z <= best
  {
    var s := digitSum(intToDigits(i));
    if s > bestSum {
      best := i;
      bestSum := s;
    } else if s == bestSum {
      if i > best {
        best := i;
      }
    }
    i := i + 1;
  }
  result := best;
}
// </vc-code>
