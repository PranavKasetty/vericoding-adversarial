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
function FindPos(s: string, k: int, start: int, current: int, target: int): bool
    requires k > 0
    requires 0 <= start < |s|
    requires start <= current < |s|
    requires start < target < |s|
    requires (current - start) % k == 0
    requires (target - start) % k == 0
    decreases target - current
{
    if current == target then true
    else if s[current] in {'G', 'T', '#'} && current != start then false
    else if current + k >= |s| then false
    else if current + k > target then false
    else FindPos(s, k, start, current + k, target)
}

lemma FindPosCorrect(s: string, k: int, start: int, current: int, target: int)
    requires k > 0
    requires 0 <= start < |s|
    requires start <= current < |s|
    requires start < target < |s|
    requires (current - start) % k == 0
    requires (target - start) % k == 0
    ensures FindPos(s, k, start, current, target) <==> 
        (forall pos :: current < pos <= target && (pos - start) % k == 0 ==> 
            (pos == target || s[pos] !in {'G', 'T', '#'}))
    decreases target - current
{
    if current == target {
    } else if s[current] in {'G', 'T', '#'} && current != start {
    } else if current + k >= |s| {
    } else if current + k > target {
    } else {
        FindPosCorrect(s, k, start, current + k, target);
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
    // Find position of G
    var gPos := -1;
    var tPos := -1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant gPos == -1 || (0 <= gPos < i && s[gPos] == 'G')
        invariant tPos == -1 || (0 <= tPos < i && s[tPos] == 'T')
        invariant gPos != -1 ==> forall j :: 0 <= j < gPos ==> s[j] != 'G'
        invariant tPos != -1 ==> forall j :: 0 <= j < tPos ==> s[j] != 'T'
    {
        if s[i] == 'G' && gPos == -1 {
            gPos := i;
        }
        if s[i] == 'T' && tPos == -1 {
            tPos := i;
        }
        i := i + 1;
    }
    
    // Determine start (G or T that comes first) and final (the other)
    var start := if gPos < tPos then gPos else tPos;
    var final := if gPos < tPos then tPos else gPos;
    
    // Check if (final - start) % k == 0
    if (final - start) % k != 0 {
        result := "NO";
        // Prove CanReachTarget is false
        assert !CanReachTarget(s, k) by {
            forall st | 0 <= st < |s| && s[st] in {'G', 'T'} && (forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'})
                ensures !(exists fin :: st < fin < |s| && s[fin] in {'G', 'T'} && (fin - st) % k == 0 && (forall pos :: st < pos < fin && (pos - st) % k == 0 ==> s[pos] !in {'G', 'T', '#'}))
            {
                // st must be start (first G or T)
                assert st == start;
                // final is the only other G or T position
                forall fin | st < fin < |s| && s[fin] in {'G', 'T'}
                    ensures fin == final
                {
                    if s[fin] == 'G' {
                        assert fin == gPos;
                        assert fin == final;
                    } else {
                        assert fin == tPos;
                        assert fin == final;
                    }
                }
                assert (final - start) % k != 0;
            }
        }
        return;
    }
    
    // Check all intermediate positions
    var canReach := true;
    var pos := start + k;
    while pos < final
        invariant start < pos
        invariant (pos - start) % k == 0
        invariant pos <= final
        invariant canReach ==> forall p :: start < p < pos && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'}
        invariant !canReach ==> exists p :: start < p < pos && (p - start) % k == 0 && s[p] in {'G', 'T', '#'}
    {
        if s[pos] in {'G', 'T', '#'} {
            canReach := false;
            break;
        }
        pos := pos + k;
    }
    
    if canReach {
        result := "YES";
        assert CanReachTarget(s, k) by {
            assert 0 <= start < |s|;
            assert s[start] in {'G', 'T'};
            assert forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'};
            assert start < final < |s|;
            assert s[final] in {'G', 'T'};
            assert (final - start) % k == 0;
            assert forall p :: start < p < final && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'};
        }
    } else {
        result := "NO";
        assert !CanReachTarget(s, k) by {
            var badPos := pos;
            assert start < badPos < final;
            assert (badPos - start) % k == 0;
            assert s[badPos] in {'G', 'T', '#'};
            forall st | 0 <= st < |s| && s[st] in {'G', 'T'} && (forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'})
                ensures !(exists fin :: st < fin < |s| && s[fin] in {'G', 'T'} && (fin - st) % k == 0 && (forall p :: st < p < fin && (p - st) % k == 0 ==> s[p] !in {'G', 'T', '#'}))
            {
                assert st == start;
                forall fin | st < fin < |s| && s[fin] in {'G', 'T'}
                    ensures fin == final
                {
                    if s[fin] == 'G' {
                        assert fin == gPos == final;
                    } else {
                        assert fin == tPos == final;
                    }
                }
                assert (final - start) % k == 0;
                assert start < badPos < final && (badPos - start) % k == 0 && s[badPos] in {'G', 'T', '#'};
            }
        }
    }
}
// </vc-code>
