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
/* helper modified by LLM (iteration 5): no helpers needed */

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
  /* code modified by LLM (iteration 5): implement solve with complete witness construction for all cases */
  var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
  
  var sum1 := digits[0] + digits[1] + digits[2];
  var sum2 := digits[3] + digits[4] + digits[5];
  
  if sum1 == sum2 {
    result := 0;
  } else {
    // Check 1 change
    var canDo1 := false;
    var witnessPos := -1;
    var witnessDigit := -1;
    var p := 0;
    while p < 6
      invariant 0 <= p <= 6
      invariant canDo1 ==> (0 <= witnessPos < 6 && 0 <= witnessDigit <= 9 &&
        (witnessPos < 3 ==> witnessDigit == sum2 - sum1 + digits[witnessPos]) &&
        (witnessPos >= 3 ==> witnessDigit == sum1 - sum2 + digits[witnessPos]))
    {
      if p < 3 {
        var needed := sum2 - sum1 + digits[p];
        if 0 <= needed <= 9 && !canDo1 {
          canDo1 := true;
          witnessPos := p;
          witnessDigit := needed;
        }
      } else {
        var needed := sum1 - sum2 + digits[p];
        if 0 <= needed <= 9 && !canDo1 {
          canDo1 := true;
          witnessPos := p;
          witnessDigit := needed;
        }
      }
      p := p + 1;
    }
    
    if canDo1 {
      result := 1;
      assert canMakeLuckyWith1Change(digits) by {
        var wp := witnessPos;
        var wd := witnessDigit;
        var newDigits := digits[..wp] + [wd] + digits[wp+1..];
        assert |newDigits| == 6;
        assert forall ii :: 0 <= ii < 6 ==> 0 <= newDigits[ii] <= 9;
        if wp < 3 {
          assert newDigits[0] + newDigits[1] + newDigits[2] == sum1 - digits[wp] + wd;
          assert newDigits[3] + newDigits[4] + newDigits[5] == sum2;
          assert wd == sum2 - sum1 + digits[wp];
          assert sum1 - digits[wp] + wd == sum2;
          assert isLucky(newDigits);
        } else {
          assert newDigits[0] + newDigits[1] + newDigits[2] == sum1;
          assert newDigits[3] + newDigits[4] + newDigits[5] == sum2 - digits[wp] + wd;
          assert wd == sum1 - sum2 + digits[wp];
          assert sum2 - digits[wp] + wd == sum1;
          assert isLucky(newDigits);
        }
      }
    } else {
      // Check 2 changes
      var canDo2 := false;
      var wi := -1;
      var wj := -1;
      var wk := -1;
      var wl := -1;
      var ii := 1;
      while ii < 6
        invariant 1 <= ii <= 6
        invariant canDo2 ==> (0 <= wj < wi < 6 && 0 <= wk <= 9 && 0 <= wl <= 9 &&
          (var nd1 := digits[..wi] + [wk] + digits[wi+1..];
           var nd2 := nd1[..wj] + [wl] + nd1[wj+1..];
           isLucky(nd2)))
      {
        var jj := 0;
        while jj < ii
          invariant 0 <= jj <= ii
          invariant canDo2 ==> (0 <= wj < wi < 6 && 0 <= wk <= 9 && 0 <= wl <= 9 &&
            (var nd1 := digits[..wi] + [wk] + digits[wi+1..];
             var nd2 := nd1[..wj] + [wl] + nd1[wj+1..];
             isLucky(nd2)))
        {
          if !canDo2 {
            // Try to find witnesses for this pair (ii, jj)
            // Compute what adjustments are needed
            // sum1_new = sum1 + (if jj<3 then wl - digits[jj] else 0) + (if ii<3 then wk - digits[ii] else 0)
            // sum2_new = sum2 + (if jj>=3 then wl - digits[jj] else 0) + (if ii>=3 then wk - digits[ii] else 0)
            // need sum1_new == sum2_new
            if ii < 3 && jj < 3 {
              // both first half: need (wk - digits[ii]) + (wl - digits[jj]) = sum2 - sum1
              var needed := sum2 - sum1;
              // try wk = digits[ii], wl = digits[jj] + needed
              var wl_try := digits[jj] + needed;
              if 0 <= wl_try <= 9 {
                var nd1 := digits[..ii] + [digits[ii]] + digits[ii+1..];
                var nd2 := nd1[..jj] + [wl_try] + nd1[jj+1..];
                assert isLucky(nd2);
                canDo2 := true; wi := ii; wj := jj; wk := digits[ii]; wl := wl_try;
              } else {
                // try wl = digits[jj], wk = digits[ii] + needed
                var wk_try := digits[ii] + needed;
                if 0 <= wk_try <= 9 {
                  var nd1 := digits[..ii] + [wk_try] + digits[ii+1..];
                  var nd2 := nd1[..jj] + [digits[jj]] + nd1[jj+1..];
                  assert isLucky(nd2);
                  canDo2 := true; wi := ii; wj := jj; wk := wk_try; wl := digits[jj];
                } else if minAdj2(digits[ii], digits[jj]) <= needed <= maxAdj2(digits[ii], digits[jj]) {
                  // split: wk = 0, wl = needed + digits[ii] + digits[jj]
                  var wk_try2 := 0;
                  var wl_try2 := needed + digits[ii] + digits[jj];
                  if 0 <= wl_try2 <= 9 {
                    var nd1 := digits[..ii] + [wk_try2] + digits[ii+1..];
                    var nd2 := nd1[..jj] + [wl_try2] + nd1[jj+1..];
                    assert isLucky(nd2);
                    canDo2 := true; wi := ii; wj := jj; wk := wk_try2; wl := wl_try2;
                  } else {
                    var wk_try3 := 9;
                    var wl_try3 := needed + digits[ii] + digits[jj] - 9 + digits[ii];
                    var wl_try4 := needed - (9 - digits[ii]) + digits[jj];
                    if 0 <= wl_try4 <= 9 {
                      var nd1 := digits[..ii] + [9] + digits[ii+1..];
                      var nd2 := nd1[..jj] + [wl_try4] + nd1[jj+1..];
                      assert isLucky(nd2);
                      canDo2 := true; wi := ii; wj := jj; wk := 9; wl := wl_try4;
                    }
                  }
                }
              }
            } else if ii >= 3 && jj >= 3 {
              // both second half: need (wk - digits[ii]) + (wl - digits[jj]) = sum1 - sum2
              var needed := sum1 - sum2;
              var wl_try := digits[jj] + needed;
              if 0 <= wl_try <= 9 {
                var nd1 := digits[..ii] + [digits[ii]] + digits[ii+1..];
                var nd2 := nd1[..jj] + [wl_try] + nd1[jj+1..];
                assert isLucky(nd2);
                canDo2 := true; wi := ii; wj := jj; wk := digits[ii]; wl := wl_try;
              } else {
                var wk_try := digits[ii] + needed;
                if 0 <= wk_try <= 9 {
                  var nd1 := digits[..ii] + [wk_try] + digits[ii+1..];
                  var nd2 := nd1[..jj] + [digits[jj]] + nd1[jj+1..];
                  assert isLucky(nd2);
                  canDo2 := true; wi := ii; wj := jj; wk := wk_try; wl := digits[jj];
                } else if minAdj2(digits[ii], digits[jj]) <= needed <= maxAdj2(digits[ii], digits[jj]) {
                  var wk_try2 := 0;
                  var wl_try2 := needed + digits[ii] + digits[jj];
                  if 0 <= wl_try2 <= 9 {
                    var nd1 := digits[..ii] + [wk_try2] + digits[ii+1..];
                    var nd2 := nd1[..jj] + [wl_try2] + nd1[jj+1..];
                    assert isLucky(nd2);
                    canDo2 := true; wi := ii; wj := jj; wk := wk_try2; wl := wl_try2;
                  } else {
                    var wl_try4 := needed - (9 - digits[ii]) + digits[jj];
                    if 0 <= wl_try4 <= 9 {
                      var nd1 := digits[..ii] + [9] + digits[ii+1..];
                      var nd2 := nd1[..jj] + [wl_try4] + nd1[jj+1..];
                      assert isLucky(nd2);
                      canDo2 := true; wi := ii; wj := jj; wk := 9; wl := wl_try4;
                    }
                  }
                }
              }
            } else {
              // ii >= 3, jj < 3 (since jj < ii)
              // sum1_new = sum1 + (wl - digits[jj]), sum2_new = sum2 + (wk - digits[ii])
              // need sum1 + wl - digits[jj] == sum2 + wk - digits[ii]
              // => wl - wk = sum2 - sum1 + digits[jj] - digits[ii]
              var target := sum2 - sum1 + digits[jj] - digits[ii];
              // wl in [0,9], wk in [0,9], wl - wk = target
              // try wk = 0, wl = target
              if 0 <= target <= 9 {
                var nd1 := digits[..ii] + [0] + digits[ii+1..];
                var nd2 := nd1[..jj] + [target] + nd1[jj+1..];
                assert isLucky(nd2);
                canDo2 := true; wi := ii; wj := jj; wk := 0; wl := target;
              } else if -9 <= target <= 0 {
                // wk = -target, wl = 0
                var wk_try := -target;
                if 0 <= wk_try <= 9 {
                  var nd1 := digits[..ii] + [wk_try] + digits[ii+1..];
                  var nd2 := nd1[..jj] + [0] + nd1[jj+1..];
                  assert isLucky(nd2);
                  canDo2 := true; wi := ii; wj := jj; wk := wk_try; wl := 0;
                }
              } else if 0 < target {
                // try wk = 9, wl = target + 9
                var wl_try := target + 9;
                if 0 <= wl_try <= 9 {
                  var nd1 := digits[..ii] + [9] + digits[ii+1..];
                  var nd2 := nd1[..jj] + [wl_try] + nd1[jj+1..];
                  assert isLucky(nd2);
                  canDo2 := true; wi := ii; wj := jj; wk := 9; wl := wl_try;
                } else {
                  // try wl = 9, wk = 9 - target
                  var wk_try := 9 - target;
                  if 0 <= wk_try <= 9 {
                    var nd1 := digits[..ii] + [wk_try] + digits[ii+1..];
                    var nd2 := nd1[..jj] + [9] + nd1[jj+1..];
                    assert isLucky(nd2);
                    canDo2 := true; wi := ii; wj := jj; wk := wk_try; wl := 9;
                  }
                }
              } else {
                // target < -9
                // try wl = 0, wk = -target
                var wk_try := -target;
                if 0 <= wk_try <= 9 {
                  var nd1 := digits[..ii] + [wk_try] + digits[ii+1..];
                  var nd2 := nd1[..jj] + [0] + nd1[jj+1..];
                  assert isLucky(nd2);
                  canDo2 := true; wi := ii; wj := jj; wk := wk_try; wl := 0;
                } else {
                  var wl_try := target + 9;
                  if 0 <= wl_try <= 9 {
                    var nd1 := digits[..ii] + [9] + digits[ii+1..];
                    var nd2 := nd1[..jj] + [wl_try] + nd1[jj+1..];
                    assert isLucky(nd2);
                    canDo2 := true; wi := ii; wj := jj; wk := 9; wl := wl_try;
                  }
                }
              }
            }
          }
          jj := jj + 1;
        }
        ii := ii + 1;
      }
      
      if canDo2 {
        result := 2;
        assert canMakeLuckyWith2Changes(digits) by {
          var nd1 := digits[..wi] + [wk] + digits[wi+1..];
          var nd2 := nd1[..wj] + [wl] + nd1[wj+1..];
          assert isLucky(nd2);
        }
        assert !canMakeLuckyWith0Changes(digits);
        assert !canMakeLuckyWith1Change(digits) by {
          forall pp | 0 <= pp < 6 ensures forall dd | 0 <= dd <= 9 ::
            !(var nd := digits[..pp] + [dd] + digits[pp+1..]; isLucky(nd))
          {
            if pp < 3 {
              var nd := digits[..pp] + [dd] + digits[pp+1..];
              assert nd[0] + nd[1] + nd[2] == sum1 - digits[pp] + dd;
              assert nd[3] + nd[4] + nd[5] == sum2;
            } else {
              var nd := digits[..pp] + [dd] + digits[pp+1..];
              assert nd[0] + nd[1] + nd[2] == sum1;
              assert nd[3] + nd[4] + nd[5] == sum2 - digits[pp] + dd;
            }
          }
        }
      } else {
        result := 3;
        assert !canMakeLuckyWith0Changes(digits);
        assert !canMakeLuckyWith1Change(digits) by {
          forall pp | 0 <= pp < 6 ensures forall dd | 0 <= dd <= 9 ::
            !(var nd := digits[..pp] + [dd] + digits[pp+1..]; isLucky(nd))
          {
            if pp < 3 {
              var nd := digits[..pp] + [dd] + digits[pp+1..];
              assert nd[0] + nd[1] + nd[2] == sum1 - digits[pp] + dd;
              assert nd[3] + nd[4] + nd[5] == sum2;
            } else {
              var nd := digits[..pp] + [dd] + digits[pp+1..];
              assert nd[0] + nd[1] + nd[2] == sum1;
              assert nd[3] + nd[4] + nd[5] == sum2 - digits[pp] + dd;
            }
          }
        }
        assert !canMakeLuckyWith2Changes(digits) by {
          forall ii2, jj2 | 0 <= jj2 < ii2 < 6 ensures forall kk, ll | 0 <= kk <= 9 && 0 <= ll <= 9 ::
            !(var nd1 := digits[..ii2] + [kk] + digits[ii2+1..];
              var nd2 := nd1[..jj2] + [ll] + nd1[jj2+1..];
              isLucky(nd2))
          {
            var nd1 := digits[..ii2] + [kk] + digits[ii2+1..];
            var nd2 := nd1[..jj2] + [ll] + nd1[jj2+1..];
            if ii2 < 3 && jj2 < 3 {
              assert nd2[0] + nd2[1] + nd2[2] == sum1 - digits[ii2] + kk - digits[jj2] + ll;
              assert nd2[3] + nd2[4] + nd2[5] == sum2;
              // need sum1 - digits[ii2] + kk - digits[jj2] + ll == sum2
              // kk + ll == sum2 - sum1 + digits[ii2] + digits[jj2]
              // min kk+ll = 0, max = 18
              // Since canDo2 is false for all pairs, the range check failed
              var needed2 := sum2 - sum1;
              var minA := (-digits[ii2]) + (-digits[jj2]);
              var maxA := (9 - digits[ii2]) + (9 - digits[jj2]);
              assert !(minA <= needed2 <= maxA);
            } else if ii2 >= 3 && jj2 >= 3 {
              assert nd2[0] + nd2[1] + nd2[2] == sum1;
              assert nd2[3] + nd2[4] + nd2[5] == sum2 - digits[ii2] + kk - digits[jj2] + ll;
              var needed2 := sum1 - sum2;
              var minA := (-digits[ii2]) + (-digits[jj2]);
              var maxA := (9 - digits[ii2]) + (9 - digits[jj2]);
              assert !(minA <= needed2 <= maxA);
            } else {
              // ii2 >= 3, jj2 < 3
              assert nd2[0] + nd2[1] + nd2[2] == sum1 - digits[jj2] + ll;
              assert nd2[3] + nd2[4] + nd2[5] == sum2 - digits[ii2] + kk;
              // need sum1 - digits[jj2] + ll == sum2 - digits[ii2] + kk
              // ll - kk == sum2 - sum1 + digits[jj2] - digits[ii2]
              var target2 := sum2 - sum1 + digits[jj2] - digits[ii2];
              var minV := 0 - 9;
              var maxV := 9 - 0;
              assert !(minV <= target2 <= maxV);
            }
          }
        }
      }
    }
  }
}
function minAdj2(a: int, b: int): int { -a + (-b) }
function maxAdj2(a: int, b: int): int { (9-a) + (9-b) }

// </vc-code>
