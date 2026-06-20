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
/* helper modified by LLM (iteration 2): Fix CanAlwaysMakeIn3Changes to handle diff==0 case and arithmetic in other cases */
lemma CanAlwaysMakeIn3Changes(digits: seq<int>)
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures canMakeLuckyWith2Changes(digits)
{
  var s1 := digits[0] + digits[1] + digits[2];
  var s2 := digits[3] + digits[4] + digits[5];
  var diff := s1 - s2;
  // We use positions i=1, j=0 (j < i)
  // Change position i to k, position j to l
  // newDigits = digits[..1] + [k] + digits[2..]
  // finalDigits = newDigits[..0] + [l] + newDigits[1..]
  // sum1_final = l + k + digits[2]
  // sum2_final = digits[3] + digits[4] + digits[5]
  // We need l + k + digits[2] == s2
  // So l + k == s2 - digits[2]
  var target := s2 - digits[2];
  // target can range from -9 to 27; we need l + k == target with 0<=k<=9, 0<=l<=9
  // So target must be in [0, 18]. Let's pick k and l.
  if target >= 0 && target <= 18 {
    var k := if target <= 9 then 0 else target - 9;
    var l := target - k;
    var nd := digits[..1] + [k] + digits[2..];
    var fd := nd[..0] + [l] + nd[1..];
    assert isLucky(fd);
  } else if target < 0 {
    // s2 - digits[2] < 0, so s2 < digits[2]
    // Try i=4, j=3 instead
    var target2 := s1 - digits[3];
    // sum1_final = s1, sum2_final = l + digits[3_new] + ...
    // newDigits = digits[..4] + [k] + digits[5..], changes pos 4
    // finalDigits = newDigits[..3] + [l] + newDigits[4..], changes pos 3
    // sum2_final = l + k + digits[5]
    // need l + k + digits[5] == s1, so l + k == s1 - digits[5]
    var tgt := s1 - digits[5];
    if tgt >= 0 && tgt <= 18 {
      var k := if tgt <= 9 then 0 else tgt - 9;
      var l := tgt - k;
      var nd := digits[..4] + [k] + digits[5..];
      var fd := nd[..3] + [l] + nd[4..];
      assert isLucky(fd);
    } else {
      // tgt < 0 means s1 < digits[5], tgt > 18 means s1 > digits[5] + 18
      // s1 <= 27, digits[5] >= 0, so s1 - digits[5] <= 27, and we need tgt <= 18
      // tgt > 18 means s1 > 18 + digits[5] >= 18
      // Use positions i=5, j=0: change pos 5 to k, pos 0 to l
      // sum1_final = l + digits[1] + digits[2]
      // sum2_final = digits[3] + digits[4] + k
      // need l + digits[1] + digits[2] == digits[3] + digits[4] + k
      // l - k == digits[3] + digits[4] - digits[1] - digits[2]
      // Let's just pick k=0, l = digits[3]+digits[4]-digits[1]-digits[2]
      // if that's in [0,9] we're done
      var lval := digits[3] + digits[4] - digits[1] - digits[2];
      if 0 <= lval <= 9 {
        var nd := digits[..5] + [0] + digits[6..];
        var fd := nd[..0] + [lval] + nd[1..];
        assert isLucky(fd);
      } else {
        // pick l=9, k = 9 - (digits[3]+digits[4]-digits[1]-digits[2]) = 9 - lval
        var kval := 9 - lval;
        if 0 <= kval <= 9 {
          var nd := digits[..5] + [kval] + digits[6..];
          var fd := nd[..0] + [9] + nd[1..];
          assert isLucky(fd);
        } else {
          // General fallback: i=5,j=2
          // sum1_final = digits[0]+digits[1]+l
          // sum2_final = digits[3]+digits[4]+k
          // need digits[0]+digits[1]+l == digits[3]+digits[4]+k
          // l - k == digits[3]+digits[4] - digits[0] - digits[1]
          var diff2 := digits[3] + digits[4] - digits[0] - digits[1];
          if diff2 >= 0 && diff2 <= 9 {
            var nd2 := digits[..5] + [0] + digits[6..];
            var fd2 := nd2[..2] + [diff2] + nd2[3..];
            assert isLucky(fd2);
          } else if diff2 < 0 {
            var nd2 := digits[..5] + [(-diff2)] + digits[6..];
            var fd2 := nd2[..2] + [0] + nd2[3..];
            assert isLucky(fd2);
          } else {
            var nd2 := digits[..5] + [9] + digits[6..];
            var fd2 := nd2[..2] + [diff2 - 9] + nd2[3..];
            assert isLucky(fd2);
          }
        }
      }
    }
  } else {
    // target > 18, meaning s2 - digits[2] > 18, so s2 > 18 + digits[2] >= 18
    // Try i=5, j=2
    var diff2 := digits[3] + digits[4] - digits[0] - digits[1];
    if diff2 >= 0 && diff2 <= 9 {
      var nd2 := digits[..5] + [0] + digits[6..];
      var fd2 := nd2[..2] + [diff2] + nd2[3..];
      assert isLucky(fd2);
    } else if diff2 < 0 {
      var nd2 := digits[..5] + [(-diff2)] + digits[6..];
      var fd2 := nd2[..2] + [0] + nd2[3..];
      assert isLucky(fd2);
    } else {
      var nd2 := digits[..5] + [9] + digits[6..];
      var fd2 := nd2[..2] + [diff2 - 9] + nd2[3..];
      assert isLucky(fd2);
    }
  }
}
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
/* code modified by LLM (iteration 2): Complete rewrite using explicit search with proper invariants */
{
  var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
  var sum1 := digits[0] + digits[1] + digits[2];
  var sum2 := digits[3] + digits[4] + digits[5];

  if sum1 == sum2 {
    result := 0;
  } else {
    // Check 1 change
    var can1 := false;
    var p1 := 0;
    var w1pos := 0;
    var w1nd := 0;
    while p1 < 6 && !can1
      invariant 0 <= p1 <= 6
      invariant can1 ==> 0 <= w1pos < 6 && 0 <= w1nd <= 9 && isLucky(digits[..w1pos] + [w1nd] + digits[w1pos+1..])
      invariant !can1 ==> forall pp :: 0 <= pp < p1 ==> forall nn :: 0 <= nn <= 9 ==> !isLucky(digits[..pp] + [nn] + digits[pp+1..])
    {
      var nd := 0;
      while nd <= 9 && !can1
        invariant 0 <= nd <= 10
        invariant can1 ==> 0 <= w1pos < 6 && 0 <= w1nd <= 9 && isLucky(digits[..w1pos] + [w1nd] + digits[w1pos+1..])
        invariant !can1 ==> forall nn :: 0 <= nn < nd ==> !isLucky(digits[..p1] + [nn] + digits[p1+1..])
      {
        var newDigits := digits[..p1] + [nd] + digits[p1+1..];
        if isLucky(newDigits) {
          can1 := true;
          w1pos := p1;
          w1nd := nd;
        }
        nd := nd + 1;
      }
      if !can1 {
        p1 := p1 + 1;
      }
    }

    if can1 {
      result := 1;
      assert canMakeLuckyWith1Change(digits) by {
        assert 0 <= w1pos < 6;
        assert 0 <= w1nd <= 9;
        assert isLucky(digits[..w1pos] + [w1nd] + digits[w1pos+1..]);
      }
    } else {
      // can1 is false, check 2 changes
      var can2 := false;
      var wi := 0;
      var wj := 0;
      var wk := 0;
      var wl := 0;
      var i2 := 1;
      while i2 < 6 && !can2
        invariant 1 <= i2 <= 6
        invariant can2 ==> 0 <= wj < wi < 6 && 0 <= wk <= 9 && 0 <= wl <= 9 &&
          (var nd2 := digits[..wi] + [wk] + digits[wi+1..]; isLucky(nd2[..wj] + [wl] + nd2[wj+1..]))
        invariant !can2 ==> forall ii, jj :: 0 <= jj < ii < i2 ==> forall kk :: 0 <= kk <= 9 ==> forall ll :: 0 <= ll <= 9 ==> var nd2 := digits[..ii] + [kk] + digits[ii+1..]; !isLucky(nd2[..jj] + [ll] + nd2[jj+1..])
      {
        var j2 := 0;
        while j2 < i2 && !can2
          invariant 0 <= j2 <= i2
          invariant can2 ==> 0 <= wj < wi < 6 && 0 <= wk <= 9 && 0 <= wl <= 9 &&
            (var nd2 := digits[..wi] + [wk] + digits[wi+1..]; isLucky(nd2[..wj] + [wl] + nd2[wj+1..]))
          invariant !can2 ==> forall jj :: 0 <= jj < j2 ==> forall kk :: 0 <= kk <= 9 ==> forall ll :: 0 <= ll <= 9 ==> var nd2 := digits[..i2] + [kk] + digits[i2+1..]; !isLucky(nd2[..jj] + [ll] + nd2[jj+1..])
        {
          var k2 := 0;
          while k2 <= 9 && !can2
            invariant 0 <= k2 <= 10
            invariant can2 ==> 0 <= wj < wi < 6 && 0 <= wk <= 9 && 0 <= wl <= 9 &&
              (var nd2 := digits[..wi] + [wk] + digits[wi+1..]; isLucky(nd2[..wj] + [wl] + nd2[wj+1..]))
            invariant !can2 ==> forall kk :: 0 <= kk < k2 ==> forall ll :: 0 <= ll <= 9 ==> var nd2 := digits[..i2] + [kk] + digits[i2+1..]; !isLucky(nd2[..j2] + [ll] + nd2[j2+1..])
          {
            var l2 := 0;
            while l2 <= 9 && !can2
              invariant 0 <= l2 <= 10
              invariant can2 ==> 0 <= wj < wi < 6 && 0 <= wk <= 9 && 0 <= wl <= 9 &&
                (var nd2 := digits[..wi] + [wk] + digits[wi+1..]; isLucky(nd2[..wj] + [wl] + nd2[wj+1..]))
              invariant !can2 ==> forall ll :: 0 <= ll < l2 ==> var nd2 := digits[..i2] + [k2] + digits[i2+1..]; !isLucky(nd2[..j2] + [ll] + nd2[j2+1..])
            {
              var nd2 := digits[..i2] + [k2] + digits[i2+1..];
              var fd2 := nd2[..j2] + [l2] + nd2[j2+1..];
              if isLucky(fd2) {
                can2 := true;
                wi := i2;
                wj := j2;
                wk := k2;
                wl := l2;
              }
              l2 := l2 + 1;
            }
            k2 := k2 + 1;
          }
          if !can2 {
            j2 := j2 + 1;
          }
        }
        if !can2 {
          i2 := i2 + 1;
        }
      }

      if can2 {
        result := 2;
        assert canMakeLuckyWith2Changes(digits) by {
          assert 0 <= wj < wi < 6;
          assert 0 <= wk <= 9;
          assert 0 <= wl <= 9;
          var nd2 := digits[..wi] + [wk] + digits[wi+1..];
          assert isLucky(nd2[..wj] + [wl] + nd2[wj+1..]);
        }
      } else {
        CanAlwaysMakeIn3Changes(digits);
        result := 3;
      }
    }
  }
}
// </vc-code>
