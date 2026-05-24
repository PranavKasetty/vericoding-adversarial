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

/* helper modified by LLM (iteration 3): fixed digitSumBound to properly recurse and use concat lemma */
lemma digitSumBound(y: int)
  requires y >= 1
  ensures digitSum(intToDigits(y)) >= 1
{
  if y < 10 {
    assert intToDigits(y) == intToDigitsHelper(y);
    assert intToDigitsHelper(y) == [y];
    assert digitSum([y]) == y + digitSum([]);
  } else {
    assert intToDigits(y) == intToDigitsHelper(y);
    assert intToDigitsHelper(y) == intToDigitsHelper(y / 10) + [y % 10];
    digitSumConcat(intToDigitsHelper(y / 10), [y % 10]);
    assert intToDigits(y / 10) == intToDigitsHelper(y / 10);
    digitSumBound(y / 10);
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
  /* code modified by LLM (iteration 3): find number with max digit sum, largest among ties */
  var best := 1;
  var bestSum := digitSum(intToDigits(1));
  digitSumBound(1);
  var i := 2;
  while i <= x
    invariant 1 <= best <= x
    invariant bestSum == digitSum(intToDigits(best))
    invariant bestSum >= 1
    invariant 1 <= i <= x + 1
    invariant forall y :: 1 <= y < i ==> digitSum(intToDigits(y)) <= bestSum
    invariant forall y :: 1 <= y < i && digitSum(intToDigits(y)) == bestSum ==> y <= best
  {
    var s := digitSum(intToDigits(i));
    digitSumBound(i);
    if s >= bestSum {
      best := i;
      bestSum := s;
    }
    i := i + 1;
  }
  result := best;
}
// </vc-code>
