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
lemma digitSumBound(x: int)
  requires x >= 1
  ensures digitSum(intToDigits(x)) >= 1
{
  if x < 10 {
    assert intToDigits(x) == intToDigitsHelper(x);
    assert intToDigitsHelper(x) == [x];
    assert digitSum([x]) == x + digitSum([]);
  } else {
    var digits := intToDigitsHelper(x);
    assert digits == intToDigitsHelper(x / 10) + [x % 10];
    digitSumConcat(intToDigitsHelper(x / 10), [x % 10]);
    digitSumBound(x / 10);
  }
}

lemma digitSumConcat(a: seq<int>, b: seq<int>)
  ensures digitSum(a + b) == digitSum(a) + digitSum(b)
{
  if |a| == 0 {
    assert a + b == b;
  } else {
    assert a + b == [a[0]] + (a[1..] + b);
    digitSumConcat(a[1..], b);
  }
}

lemma intToDigitsPositive(x: int)
  requires x >= 1
  ensures intToDigits(x) == intToDigitsHelper(x)
{
}

lemma candidateProperties(x: int)
  requires x >= 1
  ensures digitSum(intToDigits(x)) >= 1
  ensures intToDigits(x) == intToDigitsHelper(x)
{
  digitSumBound(x);
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
  requires ValidInput(x)
  ensures ValidResult(x, result)
// </vc-spec>
// <vc-code>
{
  // Find the number with maximum digit sum, and among those, the largest such number
  var best := 1;
  var bestSum := digitSum(intToDigits(1));
  var i := 2;
  while i <= x
    invariant 2 <= i <= x + 1
    invariant 1 <= best <= x
    invariant bestSum == digitSum(intToDigits(best))
    invariant forall y :: 1 <= y < i ==> digitSum(intToDigits(y)) <= bestSum
    invariant forall y :: 1 <= y < i && digitSum(intToDigits(y)) == bestSum ==> y <= best
  {
    var s := digitSum(intToDigits(i));
    if s > bestSum {
      best := i;
      bestSum := s;
    } else if s == bestSum {
      best := i;
    }
    i := i + 1;
  }
  result := best;
}
// </vc-code>
