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
predicate IsGOrT(c: char): bool { c in {'G', 'T'} }

predicate IsBlocking(c: char): bool { c in {'G', 'T', '#'} }

function FindStart(s: string): int
    requires exists i :: 0 <= i < |s| && IsGOrT(s[i])
    ensures 0 <= FindStart(s) < |s|
    ensures IsGOrT(s[FindStart(s)])
    ensures forall j :: 0 <= j < FindStart(s) ==> !IsGOrT(s[j])
{
    if IsGOrT(s[0]) then 0
    else
        var rest := FindStart(s[1..]);
        rest + 1
}

lemma FindStartCorrect(s: string)
    requires exists i :: 0 <= i < |s| && IsGOrT(s[i])
    ensures var start := FindStart(s);
        0 <= start < |s| &&
        IsGOrT(s[start]) &&
        (forall j :: 0 <= j < start ==> !IsGOrT(s[j]))
{
}

method CheckReachable(s: string, k: int, start: int) returns (reached: bool)
    requires k > 0
    requires 0 <= start < |s|
    requires IsGOrT(s[start])
    requires forall j :: 0 <= j < start ==> !IsGOrT(s[j])
    ensures reached <==> (exists final ::
        start < final < |s| &&
        IsGOrT(s[final]) &&
        (final - start) % k == 0 &&
        (forall pos :: start < pos < final && (pos - start) % k == 0 ==> !IsBlocking(s[pos]))
    )
{
    reached := false;
    var pos := start + k;
    while pos < |s|
        invariant start + k <= pos
        invariant !reached
        invariant forall final ::
            start < final < pos &&
            IsGOrT(s[final]) &&
            (final - start) % k == 0 &&
            (forall p :: start < p < final && (p - start) % k == 0 ==> !IsBlocking(s[p]))
            ==> false
        decreases |s| - pos
    {
        if IsGOrT(s[pos]) {
            // Check all intermediate steps
            var blocked := false;
            var step := start + k;
            while step < pos
                invariant start + k <= step <= pos
                invariant blocked <==> (exists p :: start < p < step && (p - start) % k == 0 && IsBlocking(s[p]))
                decreases pos - step
            {
                if IsBlocking(s[step]) {
                    blocked := true;
                }
                step := step + k;
            }
            if !blocked {
                reached := true;
                // Verify the witness
                assert IsGOrT(s[pos]);
                assert (pos - start) % k == 0;
                assert forall p :: start < p < pos && (p - start) % k == 0 ==> !IsBlocking(s[p]);
                return;
            }
            // If blocked, this final is not valid; continue
            pos := pos + k;
        } else if IsBlocking(s[pos]) {
            // '#' blocks this path, skip to next
            pos := pos + k;
        } else {
            pos := pos + k;
        }
    }
    // Prove no valid final exists
    assert !reached;
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
    var start := FindStart(s);
    FindStartCorrect(s);
    var canReach := CheckReachable(s, k, start);
    if canReach {
        result := "YES";
    } else {
        result := "NO";
    }
    // Prove equivalence with CanReachTarget
    if canReach {
        assert exists final ::
            start < final < |s| &&
            s[final] in {'G', 'T'} &&
            (final - start) % k == 0 &&
            (forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'});
        assert CanReachTarget(s, k) by {
            var final :| start < final < |s| &&
                s[final] in {'G', 'T'} &&
                (final - start) % k == 0 &&
                (forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'});
            assert 0 <= start < |s|;
            assert s[start] in {'G', 'T'};
            assert forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'};
        }
    } else {
        assert !CanReachTarget(s, k) by {
            if CanReachTarget(s, k) {
                var st :| 0 <= st < |s| &&
                    s[st] in {'G', 'T'} &&
                    (forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'}) &&
                    (exists final ::
                        st < final < |s| &&
                        s[final] in {'G', 'T'} &&
                        (final - st) % k == 0 &&
                        (forall pos :: st < pos < final && (pos - st) % k == 0 ==> s[pos] !in {'G', 'T', '#'})
                    );
                // st must equal start since both are the unique first G/T
                assert st == start by {
                    if st < start {
                        assert s[st] in {'G', 'T'};
                        assert st < start;
                        assert forall j :: 0 <= j < start ==> !IsGOrT(s[j]);
                        assert !IsGOrT(s[st]);
                        assert false;
                    }
                    if st > start {
                        assert s[start] in {'G', 'T'};
                        assert forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'};
                        assert s[start] !in {'G', 'T'};
                        assert false;
                    }
                }
                var final :| st < final < |s| &&
                    s[final] in {'G', 'T'} &&
                    (final - st) % k == 0 &&
                    (forall pos :: st < pos < final && (pos - st) % k == 0 ==> s[pos] !in {'G', 'T', '#'});
                assert start < final < |s|;
                assert s[final] in {'G', 'T'};
                assert (final - start) % k == 0;
                assert forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'};
                assert canReach;
                assert false;
            }
        }
    }
}
// </vc-code>
