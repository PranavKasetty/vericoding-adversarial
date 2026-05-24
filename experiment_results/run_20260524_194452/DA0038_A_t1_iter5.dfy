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
/* helper modified by LLM (iteration 5): simplified helpers */
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

lemma StartPosUnique(s: string, st: int)
    requires 0 <= st < |s|
    requires IsGOrT(s[st])
    requires forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'}
    requires exists i :: 0 <= i < |s| && IsGOrT(s[i])
    ensures FindStartPos(s) == st
{
    var fp := FindStartPos(s);
    if fp != st {
        if fp < st {
            assert IsGOrT(s[fp]);
            assert !IsGOrT(s[fp]);
        } else {
            assert IsGOrT(s[st]);
            assert !IsGOrT(s[st]);
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
    /* code modified by LLM (iteration 5): fix loop invariant bounds */
    var start := FindStartPos(s);
    
    var found := false;
    ghost var foundFinal := 0;
    var finalPos := start + k;
    
    while finalPos < n
        invariant start + k <= finalPos
        invariant found ==> (
            start < foundFinal < |s| &&
            s[foundFinal] in {'G', 'T'} &&
            (foundFinal - start) % k == 0 &&
            foundFinal < finalPos &&
            forall p :: start < p < foundFinal && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'}
        )
        invariant !found ==> (
            forall fp :: start + k <= fp < finalPos && fp < |s| && (fp - start) % k == 0 ==> 
                !(s[fp] in {'G', 'T'}) ||
                !(forall pos :: start < pos < fp && pos < |s| && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'})
        )
        decreases n - finalPos
    {
        if !found && IsGOrT(s[finalPos]) {
            var clear := true;
            var mid := start + k;
            while mid < finalPos
                invariant start + k <= mid <= finalPos
                invariant clear ==> forall p :: start < p < mid && p < |s| && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'}
                invariant !clear ==> exists p :: start < p < finalPos && p < |s| && (p - start) % k == 0 && s[p] in {'G', 'T', '#'}
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
                foundFinal := finalPos;
            }
        }
        finalPos := finalPos + k;
    }
    
    if found {
        assert 0 <= start < |s|;
        assert s[start] in {'G', 'T'};
        assert forall j :: 0 <= j < start ==> !IsGOrT(s[j]);
        assert forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'};
        assert start < foundFinal < |s|;
        assert s[foundFinal] in {'G', 'T'};
        assert (foundFinal - start) % k == 0;
        assert forall p :: start < p < foundFinal && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'};
        result := "YES";
    } else {
        result := "NO";
        if CanReachTarget(s, k) {
            var st :| 0 <= st < |s| && s[st] in {'G', 'T'} &&
                (forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'}) &&
                (exists fin ::
                    st < fin < |s| &&
                    s[fin] in {'G', 'T'} &&
                    (fin - st) % k == 0 &&
                    (forall pos :: st < pos < fin && (pos - st) % k == 0 ==> s[pos] !in {'G', 'T', '#'}));
            assert exists i :: 0 <= i < |s| && IsGOrT(s[i]);
            StartPosUnique(s, st);
            assert st == start;
            var fin :| st < fin < |s| && s[fin] in {'G', 'T'} && (fin - st) % k == 0 &&
                (forall pos :: st < pos < fin && (pos - st) % k == 0 ==> s[pos] !in {'G', 'T', '#'});
            assert fin >= start + k;
            assert (fin - start) % k == 0;
            assert fin < n;
            assert fin < |s|;
            assert start + k <= fin < finalPos;
            assert !(s[fin] in {'G', 'T'}) ||
                !(forall pos :: start < pos < fin && pos < |s| && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'});
            assert s[fin] in {'G', 'T'};
            assert !(forall pos :: start < pos < fin && pos < |s| && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'});
            var badPos :| start < badPos < fin && badPos < |s| && (badPos - start) % k == 0 && s[badPos] in {'G', 'T', '#'};
            assert start < badPos < fin && (badPos - start) % k == 0 && s[badPos] in {'G', 'T', '#'};
            assert false;
        }
    }
}
// </vc-code>
