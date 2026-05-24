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
/* helper modified by LLM (iteration 2): lemmas to prove division bounds for r and column */
lemma DivisionBounds(k_remaining: int, m: int, n: int)
    requires m >= 2
    requires k_remaining >= 0
    requires k_remaining < n * (m - 1)
    requires n >= 1
    ensures k_remaining / (m - 1) <= n - 1
    ensures k_remaining / (m - 1) >= 0
{
    assert m - 1 >= 1;
    assert k_remaining < n * (m - 1);
    if k_remaining / (m - 1) >= n {
        assert k_remaining / (m - 1) * (m - 1) <= k_remaining;
        assert n * (m - 1) <= k_remaining / (m - 1) * (m - 1);
        assert n * (m - 1) <= k_remaining;
        assert false;
    }
}

lemma ModBounds(k_remaining: int, m: int)
    requires m >= 2
    requires k_remaining >= 0
    ensures k_remaining % (m - 1) >= 0
    ensures k_remaining % (m - 1) <= m - 2
{
    assert m - 1 >= 1;
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
  /* code modified by LLM (iteration 2): added assertions to help verifier prove bounds */
  if k < n {
    result := [k + 1, 1];
  } else {
    var k_remaining := k - n;
    assert k_remaining >= 0;
    assert k_remaining < n * m - n;
    assert n * m - n == n * (m - 1);
    assert k_remaining < n * (m - 1);
    DivisionBounds(k_remaining, m, n);
    var r := n - k_remaining / (m - 1);
    assert r >= 1;
    assert r <= n;
    ModBounds(k_remaining, m);
    var col_offset := k_remaining % (m - 1);
    assert col_offset >= 0;
    assert col_offset <= m - 2;
    var col: int;
    if r % 2 == 1 {
      col := m - col_offset;
      assert col >= 2;
      assert col <= m;
    } else {
      col := 2 + col_offset;
      assert col >= 2;
      assert col <= m;
    }
    result := [r, col];
  }
}
// </vc-code>
