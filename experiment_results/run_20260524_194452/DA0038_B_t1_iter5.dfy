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
/* helper modified by LLM (iteration 5): fixed index out of range in loop invariants by adding < |s| bounds */
predicate IsGOrT(c: char) { c == 'G' || c == 'T' }

predicate IsBlocking(c: char) { c == 'G' || c == 'T' || c == '#' }

function FindStart(s: string): int
    requires exists i :: 0 <= i < |s| && (s[i] == 'G' || s[i] == 'T')
    ensures 0 <= FindStart(s) < |s|
    ensures s[FindStart(s)] == 'G' || s[FindStart(s)] == 'T'
    ensures forall j :: 0 <= j < FindStart(s) ==> (s[j] != 'G' && s[j] != 'T')
{
    if s[0] == 'G' || s[0] == 'T' then 0
    else
        var rest := FindStart(s[1..]);
        rest + 1
}

lemma FindStartInSet(s: string)
    requires exists i :: 0 <= i < |s| && s[i] in {'G', 'T'}
    ensures 0 <= FindStart(s) < |s|
    ensures s[FindStart(s)] in {'G', 'T'}
    ensures forall j :: 0 <= j < FindStart(s) ==> s[j] !in {'G', 'T'}
{
}

method CheckReachable(s: string, k: int, start: int) returns (reached: bool)
    requires k > 0
    requires 0 <= start < |s|
    requires s[start] == 'G' || s[start] == 'T'
    requires forall j :: 0 <= j < start ==> (s[j] != 'G' && s[j] != 'T')
    ensures reached <==> (exists final ::
        start < final < |s| &&
        (s[final] == 'G' || s[final] == 'T') &&
        (final - start) % k == 0 &&
        (forall pos :: start < pos < final && (pos - start) % k == 0 ==> (s[pos] != 'G' && s[pos] != 'T' && s[pos] != '#'))
    )
{
    reached := false;
    var pos := start + k;
    var blocked := false;
    while pos < |s|
        invariant start + k <= pos
        invariant (pos - start) % k == 0
        invariant !reached
        invariant blocked ==> (exists bp :: start < bp < pos && bp < |s| && (bp - start) % k == 0 && (s[bp] == 'G' || s[bp] == 'T' || s[bp] == '#'))
        invariant !blocked ==> (forall q :: start < q < pos && q < |s| && (q - start) % k == 0 ==> (s[q] != 'G' && s[q] != 'T' && s[q] != '#'))
        decreases |s| - pos
    {
        if s[pos] == 'G' || s[pos] == 'T' {
            if !blocked {
                reached := true;
                return;
            } else {
                break;
            }
        } else if s[pos] == '#' {
            blocked := true;
            pos := pos + k;
        } else {
            pos := pos + k;
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
  /* code modified by LLM (iteration 5): simplified proof to avoid timeout */
  var start := FindStart(s);
  FindStartInSet(s);
  assert s[start] in {'G', 'T'};
  assert forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'};
  
  var canReach := CheckReachable(s, k, start);
  
  if canReach {
    result := "YES";
    var final :| start < final < |s| &&
      (s[final] == 'G' || s[final] == 'T') &&
      (final - start) % k == 0 &&
      (forall pos :: start < pos < final && (pos - start) % k == 0 ==> (s[pos] != 'G' && s[pos] != 'T' && s[pos] != '#'));
    assert s[final] in {'G', 'T'};
    assert (forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'});
    assert CanReachTarget(s, k);
  } else {
    result := "NO";
    assert !CanReachTarget(s, k) by {
      if CanReachTarget(s, k) {
        var st :| 0 <= st < |s| && s[st] in {'G', 'T'} &&
          (forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'}) &&
          (exists fin :: st < fin < |s| && s[fin] in {'G', 'T'} && (fin - st) % k == 0 &&
            (forall pos :: st < pos < fin && (pos - st) % k == 0 ==> s[pos] !in {'G', 'T', '#'}));
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
        var fin :| st < fin < |s| && s[fin] in {'G', 'T'} && (fin - st) % k == 0 &&
          (forall pos :: st < pos < fin && (pos - st) % k == 0 ==> s[pos] !in {'G', 'T', '#'});
        assert s[fin] == 'G' || s[fin] == 'T';
        assert forall pos :: start < pos < fin && (pos - start) % k == 0 ==> (s[pos] != 'G' && s[pos] != 'T' && s[pos] != '#');
        assert false;
      }
    }
  }
}
// </vc-code>
