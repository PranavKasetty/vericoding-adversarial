// <vc-preamble>
predicate ValidInput(n: int, m: int, k: int) {
    n >= 2 && m >= 2 && n % 2 == 0 && k >= 0 && k < n * m
}

predicate ValidOutput(result: seq<int>, n: int, m: int) {
    |result| == 2 && result[0] >= 1 && result[0] <= n && result[1] >= 1 && result[1] <= m
}

predicate CorrectPosition(result: seq<int>, n: int, m: int, k: int) 
    requires ValidInput(n, m, k)
    requires |result| == 2
{
    if k < n then
        result[0] == k + 1 && result[1] == 1
    else
        var k_remaining := k - n;
        var r := n - k_remaining / (m - 1);
        result[0] == r &&
        (r % 2 == 1 ==> result[1] == m - k_remaining % (m - 1)) &&
        (r % 2 == 0 ==> result[1] == 2 + k_remaining % (m - 1))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): division bound lemma */
lemma DivisionBound(a: int, b: int, c: int)
    requires a >= 0
    requires b > 0
    requires c > 0
    requires a < b * c
    ensures a / c < b
{
    if a / c >= b {
        assert a >= (a / c) * c;
        assert (a / c) * c >= b * c;
        assert a >= b * c;
        assert false;
    }
}

lemma BoundsLemma(n: int, m: int, k: int)
    requires ValidInput(n, m, k)
    requires k >= n
    ensures var k_remaining := k - n;
            var r := n - k_remaining / (m - 1);
            var col_offset := k_remaining % (m - 1);
            r >= 1 && r <= n && col_offset >= 0 && col_offset <= m - 2
{
    var k_remaining := k - n;
    var r := n - k_remaining / (m - 1);
    var col_offset := k_remaining % (m - 1);
    assert k_remaining >= 0;
    assert k_remaining < n * (m - 1);
    DivisionBound(k_remaining, n, m - 1);
    assert k_remaining / (m - 1) < n;
    assert k_remaining / (m - 1) <= n - 1;
    assert r >= 1;
    assert r <= n;
    assert col_offset >= 0;
    assert col_offset <= m - 2;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, m, k)
    ensures ValidOutput(result, n, m)
    ensures CorrectPosition(result, n, m, k)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): use DivisionBound lemma to prove bounds */
  if k < n {
    result := [k + 1, 1];
  } else {
    var k_remaining := k - n;
    assert k_remaining >= 0;
    assert k_remaining < n * (m - 1);
    DivisionBound(k_remaining, n, m - 1);
    var r := n - k_remaining / (m - 1);
    assert k_remaining / (m - 1) <= n - 1;
    assert r >= 1;
    assert r <= n;
    var col_offset := k_remaining % (m - 1);
    assert col_offset >= 0;
    assert col_offset <= m - 2;
    var c: int;
    if r % 2 == 1 {
      c := m - col_offset;
      assert c >= 2;
      assert c <= m;
    } else {
      c := 2 + col_offset;
      assert c >= 2;
      assert c <= m;
    }
    result := [r, c];
    assert result[0] == r;
    assert result[1] == c;
    assert result[0] >= 1;
    assert result[0] <= n;
    assert result[1] >= 1;
    assert result[1] <= m;
  }
}
// </vc-code>
