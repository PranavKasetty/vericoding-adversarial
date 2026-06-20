// <vc-preamble>
predicate ValidInput(n: int, k: int, s: string)
{
    n >= 2 &&
    1 <= k < n &&
    |s| == n &&
    (exists i :: 0 <= i < |s| && s[i] == 'G') &&
    (exists i :: 0 <= i < |s| && s[i] == 'T') &&
    (forall i :: 0 <= i < |s| ==> s[i] in {'G', 'T', '.', '#'}) &&
    (forall i, j :: 0 <= i < j < |s| && s[i] == 'G' ==> s[j] != 'G') &&
    (forall i, j :: 0 <= i < j < |s| && s[i] == 'T' ==> s[j] != 'T')
}

function FindFirstGOrT(s: string): int
    requires exists i :: 0 <= i < |s| && s[i] in {'G', 'T'}
{
    if s[0] in {'G', 'T'} then 0
    else FindFirstGOrT(s[1..]) + 1
}

predicate CanReachTarget(s: string, k: int)
    requires k > 0
{
    exists start :: 
        0 <= start < |s| && 
        s[start] in {'G', 'T'} &&
        (forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'}) &&
        (exists final :: 
            start < final < |s| &&
            s[final] in {'G', 'T'} &&
            (final - start) % k == 0 &&
            (forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'})
        )
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added lemma to help with uniqueness of G/T positions */
lemma UniqueGT(s: string, start: int, final: int)
    requires 0 <= start < |s| && s[start] in {'G', 'T'}
    requires start < final < |s| && s[final] in {'G', 'T'}
    requires forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'}
    requires forall i, j :: 0 <= i < j < |s| && s[i] == 'G' ==> s[j] != 'G'
    requires forall i, j :: 0 <= i < j < |s| && s[i] == 'T' ==> s[j] != 'T'
    ensures forall fin :: start < fin < |s| && s[fin] in {'G', 'T'} ==> fin == final
    ensures forall st :: 0 <= st < |s| && s[st] in {'G', 'T'} && (forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'}) ==> st == start
{
}

// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, s: string) returns (result: string)
    requires ValidInput(n, k, s)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanReachTarget(s, k)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): simplified proof with helper lemma */
  var gPos := -1;
  var tPos := -1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant gPos == -1 || (0 <= gPos < i && s[gPos] == 'G' && forall j :: 0 <= j < gPos ==> s[j] != 'G')
    invariant tPos == -1 || (0 <= tPos < i && s[tPos] == 'T' && forall j :: 0 <= j < tPos ==> s[j] != 'T')
    invariant gPos == -1 ==> forall j :: 0 <= j < i ==> s[j] != 'G'
    invariant tPos == -1 ==> forall j :: 0 <= j < i ==> s[j] != 'T'
  {
    if s[i] == 'G' && gPos == -1 { gPos := i; }
    if s[i] == 'T' && tPos == -1 { tPos := i; }
    i := i + 1;
  }

  var start := if gPos < tPos then gPos else tPos;
  var final := if gPos < tPos then tPos else gPos;

  assert 0 <= start < |s| && s[start] in {'G', 'T'};
  assert start < final < |s| && s[final] in {'G', 'T'};
  assert forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'};

  UniqueGT(s, start, final);

  if (final - start) % k != 0 {
    result := "NO";
    assert !CanReachTarget(s, k);
    return;
  }

  var canReach := true;
  var pos := start + k;
  var badPos := -1;
  while pos < final
    invariant start < pos
    invariant (pos - start) % k == 0
    invariant pos <= final
    invariant canReach ==> forall p :: start < p < pos && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'}
    invariant !canReach ==> (badPos != -1 && start < badPos < pos && (badPos - start) % k == 0 && s[badPos] in {'G', 'T', '#'})
  {
    if s[pos] in {'G', 'T', '#'} {
      canReach := false;
      badPos := pos;
      break;
    }
    pos := pos + k;
  }

  if canReach {
    result := "YES";
    assert CanReachTarget(s, k) by {
      assert forall p :: start < p < final && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'};
    }
  } else {
    result := "NO";
    assert !canReach;
    assert badPos != -1 && start < badPos < final && (badPos - start) % k == 0 && s[badPos] in {'G', 'T', '#'};
    assert s[badPos] == '#' by {
      if s[badPos] == 'G' {
        assert forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'};
        assert start < badPos;
      }
      if s[badPos] == 'T' {
        assert forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'};
        assert start < badPos;
      }
    }
    assert !CanReachTarget(s, k) by {
      forall st | 0 <= st < |s| && s[st] in {'G', 'T'} && (forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'})
        ensures !(exists fin :: st < fin < |s| && s[fin] in {'G', 'T'} && (fin - st) % k == 0 && (forall p :: st < p < fin && (p - st) % k == 0 ==> s[p] !in {'G', 'T', '#'}))
      {
        assert st == start;
        forall fin | st < fin < |s| && s[fin] in {'G', 'T'} && (fin - st) % k == 0
          ensures exists p :: st < p < fin && (p - st) % k == 0 && s[p] in {'G', 'T', '#'}
        {
          assert fin == final;
          assert start < badPos < final && (badPos - start) % k == 0 && s[badPos] in {'G', 'T', '#'};
        }
      }
    }
  }
}

// </vc-code>
