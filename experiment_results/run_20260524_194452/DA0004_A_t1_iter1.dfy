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
  var i := 0;
  var ok := true;
  while i < n / 2
    invariant 0 <= i <= n / 2
    invariant ok <==> forall k :: 0 <= k < i ==> (
      var j := n - 1 - k;
      if s[k] == s[j] then s[k] in pal
      else (s[k] == 'p' && s[j] == 'q') || (s[k] == 'q' && s[j] == 'p') ||
           (s[k] == 'b' && s[j] == 'd') || (s[k] == 'd' && s[j] == 'b')
    )
  {
    var j := n - 1 - i;
    if s[i] == s[j] {
      if s[i] !in pal {
        ok := false;
        break;
      }
    } else if !((s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
                (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b')) {
      ok := false;
      break;
    }
    i := i + 1;
  }
  if ok {
    // Need to verify that all positions checked
    assert forall k :: 0 <= k < i ==> (
      var j := n - 1 - k;
      if s[k] == s[j] then s[k] in pal
      else (s[k] == 'p' && s[j] == 'q') || (s[k] == 'q' && s[j] == 'p') ||
           (s[k] == 'b' && s[j] == 'd') || (s[k] == 'd' && s[j] == 'b')
    );
    // If we exited normally, i == n/2
    if i == n / 2 {
      // All pairs checked
      assert forall k :: 0 <= k < n / 2 ==> (
        var j := n - 1 - k;
        if s[k] == s[j] then s[k] in pal
        else (s[k] == 'p' && s[j] == 'q') || (s[k] == 'q' && s[j] == 'p') ||
             (s[k] == 'b' && s[j] == 'd') || (s[k] == 'd' && s[j] == 'b')
      );
      // Prove is_s_palindrome(s)
      assert forall idx :: 0 <= idx < |s| ==> (
        var j := |s| - 1 - idx;
        if idx >= j then true
        else
          if s[idx] == s[j] then s[idx] in pal
          else (s[idx] == 'p' && s[j] == 'q') || (s[idx] == 'q' && s[j] == 'p') ||
               (s[idx] == 'b' && s[j] == 'd') || (s[idx] == 'd' && s[j] == 'b')
      ) by {
        forall idx | 0 <= idx < |s| {
          var j := |s| - 1 - idx;
          if idx < j {
            assert idx < n / 2;
          }
        }
      }
      result := "TAK";
    } else {
      result := "TAK";
    }
  } else {
    result := "NIE";
  }
}
// </vc-code>
