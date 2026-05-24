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
    assert intToDigits(x) == [x];
    assert digitSum([x]) == x + digitSum([]);
    assert digitSum([]) == 0;
  } else {
    var digits := intToDigits(x);
    assert digits == intToDigitsHelper(x);
    assert x % 10 >= 0;
    assert x / 10 >= 1;
    digitSumBound(x / 10);
  }
}

lemma selfIsCandidate(x: int)
  requires x >= 1
  ensures digitSum(intToDigits(x)) <= digitSum(intToDigits(x))
  ensures 1 <= x <= x
{
}

lemma maxDigitSumExists(x: int) returns (best: int)
  requires x >= 1
  ensures 1 <= best <= x
  ensures forall y :: 1 <= y <= x ==> digitSum(intToDigits(y)) <= digitSum(intToDigits(best))
  ensures forall y :: 1 <= y <= x && digitSum(intToDigits(y)) == digitSum(intToDigits(best)) ==> y <= best
{
  if x == 1 {
    best := 1;
  } else {
    var prev := maxDigitSumExists(x - 1);
    var prevSum := digitSum(intToDigits(prev));
    var xSum := digitSum(intToDigits(x));
    if xSum > prevSum {
      best := x;
    } else {
      best := prev;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
  requires ValidInput(x)
  ensures ValidResult(x, result)
// </vc-spec>
// <vc-code>
{
  var best := 1;
  var bestSum := digitSum(intToDigits(1));
  var i := 2;
  while i <= x
    invariant 2 <= i <= x + 1
    invariant 1 <= best <= x
    invariant best < i
    invariant forall y :: 1 <= y < i ==> digitSum(intToDigits(y)) <= bestSum
    invariant digitSum(intToDigits(best)) == bestSum
    invariant forall y :: 1 <= y < i && digitSum(intToDigits(y)) == bestSum ==> y <= best
  {
    var s := digitSum(intToDigits(i));
    if s > bestSum {
      best := i;
      bestSum := s;
    }
    i := i + 1;
  }
  result := best;
}
// </vc-code>
