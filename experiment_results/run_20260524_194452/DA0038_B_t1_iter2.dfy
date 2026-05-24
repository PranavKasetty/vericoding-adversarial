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

/* helper modified by LLM (iteration 2): removed invalid ': bool' return type from predicates */
predicate IsGOrT(c: char) { c in {'G', 'T'} }

predicate IsBlocking(c: char) { c in {'G', 'T', '#'} }

function FindStart(s: string): int
    requires exists i :: 0 <= i < |s| && s[i] in {'G', 'T'}
    ensures 0 <= FindStart(s) < |s|
    ensures s[FindStart(s)] in {'G', 'T'}
    ensures forall j :: 0 <= j < FindStart(s) ==> s[j] !in {'G', 'T'}
{
    if s[0] in {'G', 'T'} then 0
    else
        var rest := FindStart(s[1..]);
        rest + 1
}

method CheckReachable(s: string, k: int, start: int) returns (reached: bool)
    requires k > 0
    requires 0 <= start < |s|
    requires s[start] in {'G', 'T'}
    requires forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'}
    ensures reached <==> (exists final ::
        start < final < |s| &&
        s[final] in {'G', 'T'} &&
        (final - start) % k == 0 &&
        (forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'})
    )
{
    reached := false;
    var pos := start + k;
    ghost var blocked_at := |s|; // first blocking position on the path, |s| means none found yet
    while pos < |s|
        invariant start + k <= pos
        invariant pos == start + k * ((pos - start) / k)
        invariant blocked_at == |s| || (start < blocked_at < pos && (blocked_at - start) % k == 0 && s[blocked_at] in {'G', 'T', '#'})
        invariant blocked_at < |s| ==> forall q :: start < q < pos && (q - start) % k == 0 && s[q] in {'G', 'T'} ==> false
        invariant blocked_at == |s| ==> forall q :: start < q < pos && (q - start) % k == 0 ==> s[q] !in {'G', 'T', '#'}
        invariant reached ==> exists final :: start < final < pos && s[final] in {'G', 'T'} && (final - start) % k == 0 && (forall pp :: start < pp < final && (pp - start) % k == 0 ==> s[pp] !in {'G', 'T', '#'})
        invariant !reached
        decreases |s| - pos
    {
        if s[pos] in {'G', 'T'} {
            if blocked_at == |s| {
                reached := true;
                return;
            } else {
                // blocked, stop
                break;
            }
        } else if s[pos] in {'#'} {
            if blocked_at == |s| {
                blocked_at := pos;
            }
            pos := pos + k;
        } else {
            pos := pos + k;
        }
    }
    // prove no valid final exists
    if reached {
    } else {
        assert forall final :: start < final < |s| && s[final] in {'G', 'T'} && (final - start) % k == 0 ==> !(forall pp :: start < pp < final && (pp - start) % k == 0 ==> s[pp] !in {'G', 'T', '#'}) by {
        }
    }
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
  /* code modified by LLM (iteration 2): fixed compilation errors, implement solve using FindStart and CheckReachable */
  var start := FindStart(s);
  assert s[start] in {'G', 'T'};
  assert forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'};
  var canReach := CheckReachable(s, k, start);
  if canReach {
    result := "YES";
    assert exists final ::
      start < final < |s| &&
      s[final] in {'G', 'T'} &&
      (final - start) % k == 0 &&
      (forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'});
    assert CanReachTarget(s, k);
  } else {
    result := "NO";
    assert !CanReachTarget(s, k) by {
      if CanReachTarget(s, k) {
        var st :| 0 <= st < |s| && s[st] in {'G', 'T'} &&
          (forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'}) &&
          (exists final :: st < final < |s| && s[final] in {'G', 'T'} && (final - st) % k == 0 &&
            (forall pos :: st < pos < final && (pos - st) % k == 0 ==> s[pos] !in {'G', 'T', '#'}));
        assert st == start by {
          if st < start {
            assert s[st] in {'G', 'T'};
            assert forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'};
            assert false;
          }
          if st > start {
            assert s[start] in {'G', 'T'};
            assert forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'};
            assert false;
          }
        }
        assert false;
      }
    }
  }
}

// </vc-code>
