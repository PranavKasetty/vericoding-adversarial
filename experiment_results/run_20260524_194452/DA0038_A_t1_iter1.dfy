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

function FindStartPos(s: string): int
    requires exists i :: 0 <= i < |s| && IsGOrT(s[i])
    ensures 0 <= FindStartPos(s) < |s|
    ensures IsGOrT(s[FindStartPos(s)])
    ensures forall j :: 0 <= j < FindStartPos(s) ==> !IsGOrT(s[j])
{
    if IsGOrT(s[0]) then 0
    else
        var rest := FindStartPos(s[1..]);
        rest + 1
}

lemma FindStartPosCorrect(s: string)
    requires exists i :: 0 <= i < |s| && IsGOrT(s[i])
    ensures var start := FindStartPos(s);
            forall j :: 0 <= j < start ==> !IsGOrT(s[j])
{
}

function CanReachFromStart(s: string, start: int, k: int): bool
    requires 0 <= start < |s|
    requires k > 0
{
    exists final ::
        start < final < |s| &&
        IsGOrT(s[final]) &&
        (final - start) % k == 0 &&
        (forall pos :: start < pos < final && (pos - start) % k == 0 ==> !IsBlocking(s[pos]))
}

lemma CanReachEquiv(s: string, k: int)
    requires k > 0
    requires exists i :: 0 <= i < |s| && IsGOrT(s[i])
    ensures CanReachTarget(s, k) <==> 
        (var start := FindStartPos(s);
         CanReachFromStart(s, start, k))
{
    var start := FindStartPos(s);
    if CanReachTarget(s, k) {
        var st :| 0 <= st < |s| && IsGOrT(s[st]) &&
            (forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'}) &&
            (exists final ::
                st < final < |s| &&
                s[final] in {'G', 'T'} &&
                (final - st) % k == 0 &&
                (forall pos :: st < pos < final && (pos - st) % k == 0 ==> s[pos] !in {'G', 'T', '#'}));
        assert st == start by {
            if st < start {
                assert !IsGOrT(s[st]);
                assert false;
            }
            if st > start {
                assert forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'};
                assert s[start] in {'G', 'T'};
                assert start < st;
                assert false;
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
    var i := 0;
    // Find start position
    var start := -1;
    while i < n
        invariant 0 <= i <= n
        invariant start == -1 ==> forall j :: 0 <= j < i ==> !IsGOrT(s[j])
        invariant start != -1 ==> 0 <= start < i && IsGOrT(s[start]) && forall j :: 0 <= j < start ==> !IsGOrT(s[j])
    {
        if IsGOrT(s[i]) {
            start := i;
            break;
        }
        i := i + 1;
    }
    
    if start == -1 {
        result := "NO";
        return;
    }
    
    // Check if we can reach a different G/T from start with step k
    var found := false;
    var pos := start + k;
    while pos < n
        invariant pos >= start + k
        invariant !found ==> forall p :: start < p < pos && (p - start) % k == 0 ==> 
            (!IsGOrT(s[p]) || (exists q :: start < q < p && (q - start) % k == 0 && IsBlocking(s[q])))
    {
        if IsGOrT(s[pos]) {
            // Check all intermediate positions are non-blocking
            var clear := true;
            var mid := start + k;
            while mid < pos
                invariant start + k <= mid <= pos
                invariant clear ==> forall p :: start < p < mid && (p - start) % k == 0 ==> !IsBlocking(s[p])
            {
                if IsBlocking(s[mid]) {
                    clear := false;
                    break;
                }
                mid := mid + k;
            }
            if clear {
                found := true;
                break;
            }
        } else if IsBlocking(s[pos]) {
            // blocked, skip to next starting multiple... but we need to continue checking
            // Actually we just continue
        }
        pos := pos + k;
    }
    
    if found {
        // Need to verify CanReachTarget holds
        var finalPos := pos;
        assert 0 <= start < |s|;
        assert IsGOrT(s[start]);
        assert forall j :: 0 <= j < start ==> !IsGOrT(s[j]);
        assert start < finalPos < |s|;
        assert IsGOrT(s[finalPos]);
        assert (finalPos - start) % k == 0;
        result := "YES";
    } else {
        result := "NO";
        // Need to prove CanReachTarget is false
        // By our loop we checked all positions at multiples of k from start
        // For any candidate final, either it's blocked or not G/T
        if CanReachTarget(s, k) {
            CanReachEquiv(s, k);
            var st := FindStartPos(s);
            assert st == start;
            assert CanReachFromStart(s, start, k);
            var fin :| start < fin < |s| && IsGOrT(s[fin]) && (fin - start) % k == 0 &&
                forall p :: start < p < fin && (p - start) % k == 0 ==> !IsBlocking(s[p]);
            // fin must have been checked in our loop
            assert fin >= start + k;
            assert false;
        }
    }
}
// </vc-code>
