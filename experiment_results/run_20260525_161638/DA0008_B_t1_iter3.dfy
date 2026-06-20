// <vc-preamble>
function countLessValue(n: int, m: int, target: int): int
  requires n >= 0 && m >= 1 && target >= 1
  ensures countLessValue(n, m, target) >= 0
  ensures countLessValue(n, m, target) <= n * m
{
  if n == 0 then 0
  else 
    var maxJ := (target - 1) / n;
    var actualMaxJ := if maxJ > m then m else maxJ;
    var contribution := if actualMaxJ >= 1 then actualMaxJ else 0;
    contribution + countLessValue(n - 1, m, target)
}

function countLessOrEqualValue(n: int, m: int, target: int): int
  requires n >= 1 && m >= 1 && target >= 0
  ensures countLessOrEqualValue(n, m, target) >= 0
  ensures countLessOrEqualValue(n, m, target) <= n * m
{
  if target <= 0 then 0
  else if target >= n * m then n * m
  else countLessValue(n, m, target + 1)
}

predicate ValidInput(n: int, m: int, k: int)
{
  1 <= n <= 500000 && 1 <= m <= 500000 && 1 <= k <= n * m
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added divMonotone lemma to prove integer division monotonicity */
lemma divMonotone(a: int, b: int, d: int)
  requires 0 <= a <= b
  requires d >= 1
  ensures a / d <= b / d
{
  var qa := a / d;
  var qb := b / d;
  if qa > qb {
    calc {
      b
        >= a;
      a
        >= qa * d;
      qa * d
        > qb * d;
      qb * d
        >= b - (b % d);
    }
    assert b >= qa * d > qb * d;
    assert b / d >= qa by {
      assert b >= qa * d;
    }
    assert false;
  }
}

lemma countLessValueMonotone(n: int, m: int, t1: int, t2: int)
  requires n >= 0 && m >= 1 && t1 >= 1 && t2 >= 1
  requires t1 <= t2
  ensures countLessValue(n, m, t1) <= countLessValue(n, m, t2)
{
  if n == 0 {
  } else {
    var maxJ1 := (t1 - 1) / n;
    var actualMaxJ1 := if maxJ1 > m then m else maxJ1;
    var contribution1 := if actualMaxJ1 >= 1 then actualMaxJ1 else 0;
    var maxJ2 := (t2 - 1) / n;
    var actualMaxJ2 := if maxJ2 > m then m else maxJ2;
    var contribution2 := if actualMaxJ2 >= 1 then actualMaxJ2 else 0;
    assert t1 - 1 >= 0;
    assert t2 - 1 >= t1 - 1;
    divMonotone(t1 - 1, t2 - 1, n);
    assert maxJ1 <= maxJ2;
    assert actualMaxJ1 <= actualMaxJ2;
    assert contribution1 <= contribution2;
    countLessValueMonotone(n - 1, m, t1, t2);
  }
}

lemma countLessOrEqualMonotone(n: int, m: int, v1: int, v2: int)
  requires n >= 1 && m >= 1 && v1 >= 0 && v2 >= 0
  requires v1 <= v2
  ensures countLessOrEqualValue(n, m, v1) <= countLessOrEqualValue(n, m, v2)
{
  if v1 <= 0 {
  } else if v2 >= n * m {
  } else if v1 >= n * m {
    assert v2 >= n * m;
  } else {
    countLessValueMonotone(n, m, v1 + 1, v2 + 1);
  }
}

lemma countLessOrEqualAtNM(n: int, m: int)
  requires n >= 1 && m >= 1
  ensures countLessOrEqualValue(n, m, n * m) == n * m
{
}

lemma countLessValueAtLeast1Helper(n: int, m: int)
  requires n >= 1 && m >= 1
  ensures countLessValue(n, m, 2) >= 1
{
  if n == 1 {
    var maxJ := (2 - 1) / 1;
    var actualMaxJ := if maxJ > m then m else maxJ;
    assert actualMaxJ >= 1;
  } else {
    countLessValueAtLeast1Helper(n - 1, m);
  }
}

lemma countLessOrEqualAt1(n: int, m: int)
  requires n >= 1 && m >= 1
  ensures countLessOrEqualValue(n, m, 1) >= 1
{
  countLessValueAtLeast1Helper(n, m);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int) returns (result: int)
  requires ValidInput(n, m, k)
  ensures 1 <= result <= n * m
  ensures countLessOrEqualValue(n, m, result) >= k
  ensures result == 1 || countLessOrEqualValue(n, m, result - 1) < k
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): using monotone lemmas for binary search */
  var lo := 1;
  var hi := n * m;
  
  countLessOrEqualAtNM(n, m);
  countLessOrEqualAt1(n, m);
  
  while lo < hi
    invariant 1 <= lo <= hi <= n * m
    invariant countLessOrEqualValue(n, m, hi) >= k
    invariant lo == 1 || countLessOrEqualValue(n, m, lo - 1) < k
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    var cnt := countLessOrEqualValue(n, m, mid);
    if cnt >= k {
      hi := mid;
    } else {
      lo := mid + 1;
    }
  }
  
  result := lo;
}
// </vc-code>
