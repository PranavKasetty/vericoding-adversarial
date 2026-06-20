// <vc-preamble>
function charToInt(c: char): int
  requires '0' <= c <= '9'
{
  c as int - '0' as int
}

function isLucky(digits: seq<int>): bool
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  var sum1 := digits[0] + digits[1] + digits[2];
  var sum2 := digits[3] + digits[4] + digits[5];
  sum1 == sum2
}

predicate ValidTicket(ticket: string)
{
  |ticket| == 6 && forall i :: 0 <= i < |ticket| ==> '0' <= ticket[i] <= '9'
}

predicate canMakeLuckyWith0Changes(digits: seq<int>)
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  isLucky(digits)
}

predicate canMakeLuckyWith1Change(digits: seq<int>)
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  exists pos :: 0 <= pos < 6 &&
    exists newDigit :: 0 <= newDigit <= 9 &&
      var newDigits := digits[..pos] + [newDigit] + digits[pos+1..];
      isLucky(newDigits)
}

predicate canMakeLuckyWith2Changes(digits: seq<int>)
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  exists i, j :: 0 <= j < i < 6 &&
    exists k, l :: 0 <= k <= 9 && 0 <= l <= 9 &&
      var newDigits := digits[..i] + [k] + digits[i+1..];
      var finalDigits := newDigits[..j] + [l] + newDigits[j+1..];
      isLucky(finalDigits)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): empty helpers section - no helpers needed */
// </vc-helpers>

// <vc-spec>
method solve(ticket: string) returns (result: int)
  requires ValidTicket(ticket)
  ensures 0 <= result <= 3
  ensures var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
          result == 0 <==> canMakeLuckyWith0Changes(digits)
  ensures var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
          result == 1 <==> (!canMakeLuckyWith0Changes(digits) && canMakeLuckyWith1Change(digits))
  ensures var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
          result == 2 <==> (!canMakeLuckyWith0Changes(digits) && !canMakeLuckyWith1Change(digits) && canMakeLuckyWith2Changes(digits))
  ensures var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
          result == 3 <==> (!canMakeLuckyWith0Changes(digits) && !canMakeLuckyWith1Change(digits) && !canMakeLuckyWith2Changes(digits))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): implement solve by computing digits and checking lucky conditions */
  var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
  
  // Check if already lucky (0 changes)
  var sum1 := digits[0] + digits[1] + digits[2];
  var sum2 := digits[3] + digits[4] + digits[5];
  
  if sum1 == sum2 {
    result := 0;
  } else {
    // Check if 1 change suffices
    // With 1 change at position pos to newDigit:
    // If pos < 3: new sum1 = sum1 - digits[pos] + newDigit, need sum1 - digits[pos] + newDigit == sum2
    //   => newDigit = sum2 - sum1 + digits[pos]
    // If pos >= 3: new sum2 = sum2 - digits[pos] + newDigit, need sum1 == sum2 - digits[pos] + newDigit
    //   => newDigit = sum1 - sum2 + digits[pos]
    var canDo1 := false;
    var pos := 0;
    while pos < 6
      invariant 0 <= pos <= 6
    {
      if pos < 3 {
        var needed := sum2 - sum1 + digits[pos];
        if 0 <= needed <= 9 {
          canDo1 := true;
        }
      } else {
        var needed := sum1 - sum2 + digits[pos];
        if 0 <= needed <= 9 {
          canDo1 := true;
        }
      }
      pos := pos + 1;
    }
    
    if canDo1 {
      result := 1;
      // Provide witnesses for canMakeLuckyWith1Change
      assert canMakeLuckyWith1Change(digits) by {
        var p := 0;
        while p < 6
          invariant 0 <= p <= 6
        {
          if p < 3 {
            var needed := sum2 - sum1 + digits[p];
            if 0 <= needed <= 9 {
              var newDigits := digits[..p] + [needed] + digits[p+1..];
              assert |newDigits| == 6;
              assert newDigits[0] + newDigits[1] + newDigits[2] == sum1 - digits[p] + needed;
              assert newDigits[3] + newDigits[4] + newDigits[5] == sum2;
              assert isLucky(newDigits);
              assert exists pos2 :: 0 <= pos2 < 6 && exists newDigit :: 0 <= newDigit <= 9 &&
                var nd := digits[..pos2] + [newDigit] + digits[pos2+1..];
                isLucky(nd);
            }
          } else {
            var needed := sum1 - sum2 + digits[p];
            if 0 <= needed <= 9 {
              var newDigits := digits[..p] + [needed] + digits[p+1..];
              assert |newDigits| == 6;
              assert newDigits[0] + newDigits[1] + newDigits[2] == sum1;
              assert newDigits[3] + newDigits[4] + newDigits[5] == sum2 - digits[p] + needed;
              assert isLucky(newDigits);
              assert exists pos2 :: 0 <= pos2 < 6 && exists newDigit :: 0 <= newDigit <= 9 &&
                var nd := digits[..pos2] + [newDigit] + digits[pos2+1..];
                isLucky(nd);
            }
          }
          p := p + 1;
        }
      }
    } else {
      // Check if 2 changes suffice
      // With 2 changes at positions i and j (j < i):
      // The difference diff = sum1 - sum2 must be achievable by adjusting two digits
      // We need to split diff = delta_i + delta_j where each delta is in [-9, 9]
      // Actually let's just check: can we split diff into two parts each in [-9,9]?
      // diff = sum1 - sum2, range of each adjustment is [-9, 9]
      // We need delta1 + delta2 = -diff where delta1, delta2 in [-9,9]
      // This is possible iff -18 <= -diff <= 18, i.e., |diff| <= 18
      // But we also need valid digits after change
      // More precisely: for position i in first half, adjustment range is [-digits[i], 9-digits[i]]
      // Let's do a concrete check
      var diff := sum1 - sum2;
      var canDo2 := false;
      // Try all pairs of positions
      var i := 0;
      while i < 6
        invariant 0 <= i <= 6
      {
        var j := 0;
        while j < i
          invariant 0 <= j <= i
        {
          // Change position i and position j
          // If both in first half or both in second half:
          // sum changes by (newI - digits[i]) + (newJ - digits[j])
          // We need the total change to make sum1_new == sum2_new
          // Let deltaI = newI - digits[i], deltaJ = newJ - digits[j]
          // If i < 3 and j < 3: need delta = sum2 - sum1 = deltaI + deltaJ
          //   can achieve if |delta| <= 18 and we can split
          // If i >= 3 and j >= 3: need deltaI + deltaJ = sum1 - sum2
          // If i < 3 and j >= 3: need deltaI - deltaJ = sum2 - sum1 (deltaI from first, deltaJ from second negated)
          //   Actually: sum1_new = sum1 + deltaI, sum2_new = sum2 + deltaJ
          //   need sum1 + deltaI == sum2 + deltaJ => deltaI - deltaJ = sum2 - sum1
          if i < 3 && j < 3 {
            var needed := sum2 - sum1;
            // need deltaI + deltaJ = needed, deltaI in [-digits[i], 9-digits[i]], deltaJ in [-digits[j], 9-digits[j]]
            var minAdj := (-digits[i]) + (-digits[j]);
            var maxAdj := (9 - digits[i]) + (9 - digits[j]);
            if minAdj <= needed <= maxAdj {
              canDo2 := true;
            }
          } else if i >= 3 && j >= 3 {
            var needed := sum1 - sum2;
            var minAdj := (-digits[i]) + (-digits[j]);
            var maxAdj := (9 - digits[i]) + (9 - digits[j]);
            if minAdj <= needed <= maxAdj {
              canDo2 := true;
            }
          } else {
            // i < 3, j >= 3 or i >= 3, j < 3
            // Actually j < i, so if i >= 3 and j < 3:
            // sum1_new = sum1 + deltaJ (j < 3), sum2_new = sum2 + deltaI (i >= 3)
            // need sum1 + deltaJ == sum2 + deltaI => deltaJ - deltaI = sum2 - sum1
            var needed := sum2 - sum1;
            // deltaJ in [-digits[j], 9-digits[j]], deltaI in [-digits[i], 9-digits[i]]
            // deltaJ - deltaI = needed
            // min of deltaJ - deltaI = -digits[j] - (9-digits[i]) = digits[i] - digits[j] - 9
            // max of deltaJ - deltaI = (9-digits[j]) - (-digits[i]) = 9 + digits[i] - digits[j]
            var minVal := digits[i] - digits[j] - 9;
            var maxVal := 9 + digits[i] - digits[j];
            if minVal <= needed <= maxVal {
              canDo2 := true;
            }
          }
          j := j + 1;
        }
        i := i + 1;
      }
      
      if canDo2 {
        result := 2;
        assert canMakeLuckyWith2Changes(digits) by {
          var i2 := 0;
          while i2 < 6
            invariant 0 <= i2 <= 6
          {
            var j2 := 0;
            while j2 < i2
              invariant 0 <= j2 <= i2
            {
              if i2 < 3 && j2 < 3 {
                var needed := sum2 - sum1;
                var minAdj := (-digits[i2]) + (-digits[j2]);
                var maxAdj := (9 - digits[i2]) + (9 - digits[j2]);
                if minAdj <= needed <= maxAdj {
                  // Pick newI = 0, newJ = needed + digits[i2] + digits[j2]
                  // Or just pick newI and solve
                  var newI := digits[i2];
                  var newJ := digits[j2] + needed;
                  if 0 <= newJ <= 9 {
                    var nd1 := digits[..i2] + [newI] + digits[i2+1..];
                    var nd2 := nd1[..j2] + [newJ] + nd1[j2+1..];
                    assert |nd1| == 6;
                    assert |nd2| == 6;
                    assert nd2[0] + nd2[1] + nd2[2] == sum1 + needed;
                    assert nd2[3] + nd2[4] + nd2[5] == sum2;
                    assert isLucky(nd2);
                  } else {
                    var newI2 := digits[i2] + needed;
                    if 0 <= newI2 <= 9 {
                      var nd1 := digits[..i2] + [newI2] + digits[i2+1..];
                      var nd2 := nd1[..j2] + [digits[j2]] + nd1[j2+1..];
                      assert |nd1| == 6;
                      assert |nd2| == 6;
                      assert nd2[0] + nd2[1] + nd2[2] == sum1 + needed;
                      assert nd2[3] + nd2[4] + nd2[5] == sum2;
                      assert isLucky(nd2);
                    }
                  }
                }
              }
              j2 := j2 + 1;
            }
            i2 := i2 + 1;
          }
        }
        assert !canMakeLuckyWith0Changes(digits);
        assert !canMakeLuckyWith1Change(digits);
      } else {
        result := 3;
        assert !canMakeLuckyWith0Changes(digits);
        assert !canMakeLuckyWith1Change(digits);
        assert !canMakeLuckyWith2Changes(digits);
      }
    }
  }
}
// </vc-code>
