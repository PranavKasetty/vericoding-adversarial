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
/* helper modified by LLM (iteration 4): simplified divMonotone using direct arithmetic reasoning */
lemma divMonotone(a: int, b: int, d: int)
  requires 0 <= a <= b
  requires d >= 1
  ensures a / d <= b / d
{
  var diff := b - a;
  assert b == a + diff;
  assert a / d <= (a + diff) / d by {
    assert a + diff == b;
    var qa := a / d;
    var ra := a % d;
    assert a == qa * d + ra;
    assert 0 <= ra < d;
    assert b >= a == qa * d + ra;
    assert b / d >= qa by {
      assert b >= qa * d;
      assert b / d * d <= b;
      if b / d < qa {
        assert b / d <= qa - 1;
        assert b / d * d <= (qa - 1) * d;
        assert b < qa * d;
        assert false;
      }
    }
  }
}

lemma countLessValueMonotone(n: int, m: int, t1: int, t2: int)
  requires n >= 0 && m >= 1 && t1 >= 1 && t2 >= 1
  requires t1 <= t2
  ensures countLessValue(n, m, t1) <= countLessValue(n, m, t2)
{
  if n == 0 {
  } else {
    divMonotone(t1 - 1, t2 - 1, n);
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
    assert (2 - 1) / 1 == 1;
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
  /* code modified by LLM (iteration 4): binary search using monotone lemmas */
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
      countLessOrEqualMonotone(n, m, mid, lo + (hi - lo) / 2);
      lo := mid + 1;
    }
  }
  
  result := lo;
}
// </vc-code>
