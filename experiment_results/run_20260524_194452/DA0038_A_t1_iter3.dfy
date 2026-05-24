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
/* helper modified by LLM (iteration 3): simplified helpers */
predicate IsGOrT(c: char) { c in {'G', 'T'} }

predicate IsBlocking(c: char) { c in {'G', 'T', '#'} }

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

predicate PathClear(s: string, start: int, final: int, k: int)
    requires 0 <= start < final < |s|
    requires k > 0
{
    forall pos :: start < pos < final && (pos - start) % k == 0 ==> !IsBlocking(s[pos])
}

lemma StartUnique(s: string, st: int)
    requires 0 <= st < |s|
    requires IsGOrT(s[st])
    requires forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'}
    requires exists i :: 0 <= i < |s| && IsGOrT(s[i])
    ensures FindStartPos(s) == st
{
    var fp := FindStartPos(s);
    if fp < st {
        assert IsGOrT(s[fp]);
        assert fp < st;
        assert s[fp] !in {'G', 'T'};
        assert false;
    }
    if fp > st {
        assert forall j :: 0 <= j < fp ==> !IsGOrT(s[j]);
        assert st < fp;
        assert IsGOrT(s[st]);
        assert false;
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
    /* code modified by LLM (iteration 3): clean implementation using FindStartPos */
    var start := FindStartPos(s);
    
    var found := false;
    var finalPos := start + k;
    
    while finalPos < n
        invariant start + k <= finalPos
        invariant !found
        decreases n - finalPos
    {
        if IsGOrT(s[finalPos]) {
            // Check if path is clear
            var clear := true;
            var mid := start + k;
            while mid < finalPos
                invariant start + k <= mid <= finalPos
                invariant clear ==> forall p :: start < p < mid && (p - start) % k == 0 ==> !IsBlocking(s[p])
                decreases finalPos - mid
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
        }
        finalPos := finalPos + k;
    }
    
    if found {
        // Prove CanReachTarget
        assert 0 <= start < |s|;
        assert s[start] in {'G', 'T'};
        assert forall j :: 0 <= j < start ==> !IsGOrT(s[j]);
        assert start < finalPos < |s|;
        assert s[finalPos] in {'G', 'T'};
        assert (finalPos - start) % k == 0;
        assert forall p :: start < p < finalPos && (p - start) % k == 0 ==> !IsBlocking(s[p]);
        assert forall p :: start < p < finalPos && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'};
        result := "YES";
    } else {
        result := "NO";
        // Prove !CanReachTarget
        if CanReachTarget(s, k) {
            var st :| 0 <= st < |s| && s[st] in {'G', 'T'} &&
                (forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'}) &&
                (exists fin ::
                    st < fin < |s| &&
                    s[fin] in {'G', 'T'} &&
                    (fin - st) % k == 0 &&
                    (forall pos :: st < pos < fin && (pos - st) % k == 0 ==> s[pos] !in {'G', 'T', '#'}));
            StartUnique(s, st);
            assert st == start;
            var fin :| st < fin < |s| && s[fin] in {'G', 'T'} && (fin - st) % k == 0 &&
                (forall pos :: st < pos < fin && (pos - st) % k == 0 ==> s[pos] !in {'G', 'T', '#'});
            assert fin >= start + k;
            // fin should have been found in our loop
            assert false;
        }
    }
}
// </vc-code>
