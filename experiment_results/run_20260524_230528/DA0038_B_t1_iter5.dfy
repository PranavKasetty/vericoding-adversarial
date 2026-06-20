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
/* helper modified by LLM (iteration 5): UniqueGT lemma with explicit proof */
lemma UniqueGT(s: string, start: int, final: int)
    requires 0 <= start < |s| && s[start] in {'G', 'T'}
    requires start < final < |s| && s[final] in {'G', 'T'}
    requires forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'}
    requires forall i, j :: 0 <= i < j < |s| && s[i] == 'G' ==> s[j] != 'G'
    requires forall i, j :: 0 <= i < j < |s| && s[i] == 'T' ==> s[j] != 'T'
    ensures forall fin :: start < fin < |s| && s[fin] in {'G', 'T'} ==> fin == final
    ensures forall st :: 0 <= st < |s| && s[st] in {'G', 'T'} && (forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'}) ==> st == start
{
    forall fin | start < fin < |s| && s[fin] in {'G', 'T'}
        ensures fin == final
    {
        if fin != final {
            if s[fin] == 'G' && s[final] == 'G' {
                if fin < final {
                    assert s[fin] == 'G' && fin < final && s[final] == 'G';
                } else {
                    assert s[final] == 'G' && final < fin && s[fin] == 'G';
                }
            } else if s[fin] == 'T' && s[final] == 'T' {
                if fin < final {
                    assert s[fin] == 'T' && fin < final && s[final] == 'T';
                } else {
                    assert s[final] == 'T' && final < fin && s[fin] == 'T';
                }
            } else if s[fin] == 'G' && s[final] == 'T' {
                // Both G and T exist: s[start] is either G or T
                // s[fin] == G, s[final] == T, both > start
                // s[start] must be the other one
                // No contradiction from uniqueness constraints directly
                // But we have exactly one G and one T in s
                // s[start] in {G,T}, s[fin]==G, s[final]==T
                // If s[start]==G then two G's: start and fin
                if s[start] == 'G' {
                    assert s[start] == 'G' && start < fin && s[fin] == 'G';
                } else {
                    // s[start] == T, s[final] == T, start < final
                    assert s[start] == 'T' && start < final && s[final] == 'T';
                }
            } else {
                // s[fin] == 'T' && s[final] == 'G'
                if s[start] == 'T' {
                    assert s[start] == 'T' && start < fin && s[fin] == 'T';
                } else {
                    assert s[start] == 'G' && start < final && s[final] == 'G';
                }
            }
        }
    }
    forall st | 0 <= st < |s| && s[st] in {'G', 'T'} && (forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'})
        ensures st == start
    {
        if st != start {
            if st < start {
                assert s[st] in {'G', 'T'} && st < start;
                assert s[st] !in {'G', 'T'};
            } else {
                // st > start
                assert s[start] in {'G', 'T'} && 0 <= start < st;
                assert s[start] !in {'G', 'T'};
            }
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
  /* code modified by LLM (iteration 5): restructured to reduce verification complexity */
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
    return;
  }

  var canReach := true;
  var pos := start + k;
  var badPos := -1;
  while pos < final
    invariant start < pos
    invariant (pos - start) % k == 0
    invariant pos <= final + k
    invariant canReach ==> pos <= final
    invariant canReach ==> forall p :: start < p < pos && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'}
    invariant !canReach ==> (badPos != -1 && start < badPos < final && (badPos - start) % k == 0 && s[badPos] in {'G', 'T', '#'})
    invariant !canReach ==> badPos < pos
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
    assert forall p :: start < p < final && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'};
    assert CanReachTarget(s, k);
  } else {
    result := "NO";
    assert badPos != -1 && start < badPos < final && (badPos - start) % k == 0 && s[badPos] in {'G', 'T', '#'};
    // Prove badPos is not G or T
    assert s[badPos] != 'G' by {
      if s[badPos] == 'G' {
        if s[start] == 'G' {
          // Two G's at positions start and badPos, start < badPos
          assert false;
        } else {
          // s[start] == 'T', but then we need another G
          // forall j < start: s[j] != 'G' and s[j] != 'T'
          // s[badPos] == 'G' means s[final] must be 'T' (since final is the other GT)
          // but UniqueGT says final is the unique GT after start
          // badPos < final and s[badPos] == 'G' in {'G','T'}, so by UniqueGT badPos == final, contradiction
          assert s[badPos] in {'G', 'T'};
          assert badPos == final;
          assert badPos < final;
          assert false;
        }
      }
    }
    assert s[badPos] != 'T' by {
      if s[badPos] == 'T' {
        if s[start] == 'T' {
          assert false;
        } else {
          assert s[badPos] in {'G', 'T'};
          assert badPos == final;
          assert badPos < final;
          assert false;
        }
      }
    }
    assert s[badPos] == '#';
    assert !CanReachTarget(s, k) by {
      forall st | 0 <= st < |s| && s[st] in {'G', 'T'} && (forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'})
        ensures !(exists fin :: st < fin < |s| && s[fin] in {'G', 'T'} && (fin - st) % k == 0 && (forall p :: st < p < fin && (p - st) % k == 0 ==> s[p] !in {'G', 'T', '#'}))
      {
        assert st == start;
        forall fin | st < fin < |s| && s[fin] in {'G', 'T'} && (fin - st) % k == 0
          ensures exists p :: st < p < fin && (p - st) % k == 0 && s[p] in {'G', 'T', '#'}
        {
          assert fin == final;
          assert s[badPos] == '#';
          assert s[badPos] in {'G', 'T', '#'};
          assert st < badPos < fin;
          assert (badPos - st) % k == 0;
        }
      }
    }
  }
}
// </vc-code>
