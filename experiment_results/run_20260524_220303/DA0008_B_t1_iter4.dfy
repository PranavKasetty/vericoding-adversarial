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
/* helper modified by LLM (iteration 3): fixed typo countLessFile -> countLessValue in countLessOrEqualAtOne lemma */
lemma divMonotone(a: int, b: int, n: int)
  requires a >= 0 && b >= 0 && n >= 1
  requires a <= b
  ensures a / n <= b / n
{
  var qa := a / n;
  var qb := b / n;
  if qa > qb {
    calc {
      a;
      >= qa * n;
      > qb * n;
      > b;
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
    var maxJ1 := (t1 - 1) / n;
    var actualMaxJ1 := if maxJ1 > m then m else maxJ1;
    var contribution1 := if actualMaxJ1 >= 1 then actualMaxJ1 else 0;
    var maxJ2 := (t2 - 1) / n;
    var actualMaxJ2 := if maxJ2 > m then m else maxJ2;
    var contribution2 := if actualMaxJ2 >= 1 then actualMaxJ2 else 0;
    divMonotone(t1 - 1, t2 - 1, n);
    assert (t1 - 1) / n <= (t2 - 1) / n;
    assert contribution1 <= contribution2;
    countLessValueMonotone(n - 1, m, t1, t2);
  }
}

lemma countLessOrEqualMonotone(n: int, m: int, t1: int, t2: int)
  requires n >= 1 && m >= 1 && t1 >= 0 && t2 >= 0
  requires t1 <= t2
  ensures countLessOrEqualValue(n, m, t1) <= countLessOrEqualValue(n, m, t2)
{
  if t1 <= 0 {
  } else if t2 >= n * m {
  } else if t1 >= n * m {
    assert t1 == n * m;
    assert t2 >= n * m;
  } else {
    assert t1 >= 1 && t2 >= 1;
    assert t1 + 1 >= 1 && t2 + 1 >= 1;
    countLessValueMonotone(n, m, t1 + 1, t2 + 1);
  }
}

lemma countLessOrEqualAtNM(n: int, m: int)
  requires n >= 1 && m >= 1
  ensures countLessOrEqualValue(n, m, n * m) == n * m
{
}

lemma countLessOrEqualAtOne(n: int, m: int)
  requires n >= 1 && m >= 1
  ensures countLessOrEqualValue(n, m, 1) >= 1
{
  assert countLessOrEqualValue(n, m, 1) == countLessValue(n, m, 2);
  var maxJ := (2 - 1) / n;
  if n == 1 {
    assert maxJ == 1;
    assert countLessValue(1, m, 2) == 1;
  } else {
    assert (2 - 1) / n == 0;
    var actualMaxJ := if maxJ > m then m else maxJ;
    var contribution := if actualMaxJ >= 1 then actualMaxJ else 0;
    assert contribution == 0;
    countLessOrEqualAtOne(n - 1, m);
    assert countLessValue(n, m, 2) == contribution + countLessValue(n - 1, m, 2);
    assert countLessValue(n - 1, m, 2) == countLessOrEqualValue(n - 1, m, 1);
  }
}

lemma countLessOrEqualSucc(n: int, m: int, t: int)
  requires n >= 1 && m >= 1 && t >= 1 && t < n * m
  ensures countLessOrEqualValue(n, m, t) <= countLessOrEqualValue(n, m, t + 1)
{
  countLessOrEqualMonotone(n, m, t, t + 1);
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
  /* code modified by LLM (iteration 3): binary search with monotonicity lemmas */
  countLessOrEqualAtNM(n, m);
  countLessOrEqualAtOne(n, m);
  
  var lo := 1;
  var hi := n * m;
  
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
      countLessOrEqualMonotone(n, m, mid, mid + 1);
      lo := mid + 1;
    }
  }
  
  result := lo;
}
// </vc-code>
