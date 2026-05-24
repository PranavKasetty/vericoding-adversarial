// <vc-preamble>
predicate is_s_palindrome(s: string)
{
    var pal := "AHIMOoTUVvWwXxY";

    forall i :: 0 <= i < |s| ==> 
        var j := |s| - 1 - i;
        if i >= j then true
        else
            if s[i] == s[j] then s[i] in pal
            else (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
                 (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b')
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| >= 1
    ensures result == "TAK" || result == "NIE"
    ensures result == "TAK" <==> is_s_palindrome(s)
// </vc-spec>
// <vc-code>
{
  var pal := "AHIMOoTUVvWwXxY";
  var n := |s|;
  var ok := true;
  var i := 0;
  while i < n / 2
    invariant 0 <= i <= n / 2
    invariant ok <==> forall k :: 0 <= k < i =>
      var j := n - 1 - k;
      if k >= j then true
      else
        if s[k] == s[j] then s[k] in pal
        else (s[k] == 'p' && s[j] == 'q') || (s[k] == 'q' && s[j] == 'p') ||
             (s[k] == 'b' && s[j] == 'd') || (s[k] == 'd' && s[j] == 'b')
  {
    var j := n - 1 - i;
    if i >= j {
      // nothing to check
    } else if s[i] == s[j] {
      if s[i] !in pal {
        ok := false;
      }
    } else if (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
              (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b') {
      // ok
    } else {
      ok := false;
    }
    i := i + 1;
  }
  // Now verify the full predicate holds
  // We need to handle indices where i >= j (middle elements) which are always true
  // The predicate quantifies over all i, but for i >= j it's trivially true
  // We checked all i < n/2, for i >= n/2 we have i >= j so condition is true
  if ok {
    // Prove is_s_palindrome(s)
    assert forall k :: 0 <= k < n =>
      var j := n - 1 - k;
      if k >= j then true
      else
        if s[k] == s[j] then s[k] in pal
        else (s[k] == 'p' && s[j] == 'q') || (s[k] == 'q' && s[j] == 'p') ||
             (s[k] == 'b' && s[j] == 'd') || (s[k] == 'd' && s[j] == 'b')
    by {
      forall k | 0 <= k < n
        ensures var j := n - 1 - k;
          if k >= j then true
          else
            if s[k] == s[j] then s[k] in pal
            else (s[k] == 'p' && s[j] == 'q') || (s[k] == 'q' && s[j] == 'p') ||
                 (s[k] == 'b' && s[j] == 'd') || (s[k] == 'd' && s[j] == 'b')
      {
        var j := n - 1 - k;
        if k >= j {
          // trivially true
        } else {
          // k < j means k < n/2
          assert k < n / 2;
        }
      }
    }
    result := "TAK";
  } else {
    result := "NIE";
  }
}
// </vc-code>
