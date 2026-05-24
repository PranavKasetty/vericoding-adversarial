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
/* helper modified by LLM (iteration 5): lemmas for sequence update sum properties */
lemma SeqUpdateSum1(digits: seq<int>, pos: int, newVal: int)
  requires |digits| == 6
  requires forall i :: 0 <= i < 6 ==> 0 <= digits[i] <= 9
  requires 0 <= pos < 3
  requires 0 <= newVal <= 9
  ensures var nd := digits[..pos] + [newVal] + digits[pos+1..];
          |nd| == 6 && (forall i :: 0 <= i < 6 ==> 0 <= nd[i] <= 9) &&
          nd[0] + nd[1] + nd[2] == digits[0] + digits[1] + digits[2] - digits[pos] + newVal &&
          nd[3] + nd[4] + nd[5] == digits[3] + digits[4] + digits[5]
{
  var nd := digits[..pos] + [newVal] + digits[pos+1..];
  assert nd[pos] == newVal;
  assert nd[3] == digits[3];
  assert nd[4] == digits[4];
  assert nd[5] == digits[5];
}

lemma SeqUpdateSum2(digits: seq<int>, pos: int, newVal: int)
  requires |digits| == 6
  requires forall i :: 0 <= i < 6 ==> 0 <= digits[i] <= 9
  requires 3 <= pos < 6
  requires 0 <= newVal <= 9
  ensures var nd := digits[..pos] + [newVal] + digits[pos+1..];
          |nd| == 6 && (forall i :: 0 <= i < 6 ==> 0 <= nd[i] <= 9) &&
          nd[0] + nd[1] + nd[2] == digits[0] + digits[1] + digits[2] &&
          nd[3] + nd[4] + nd[5] == digits[3] + digits[4] + digits[5] - digits[pos] + newVal
{
  var nd := digits[..pos] + [newVal] + digits[pos+1..];
  assert nd[0] == digits[0];
  assert nd[1] == digits[1];
  assert nd[2] == digits[2];
  assert nd[pos] == newVal;
}

lemma NdInRange(digits: seq<int>, ai: int, vi_try: int)
  requires |digits| == 6
  requires forall i :: 0 <= i < 6 ==> 0 <= digits[i] <= 9
  requires 0 <= ai < 6
  requires 0 <= vi_try <= 9
  ensures var nd := digits[..ai] + [vi_try] + digits[ai+1..];
          |nd| == 6 && forall i :: 0 <= i < 6 ==> 0 <= nd[i] <= 9
{
  var nd := digits[..ai] + [vi_try] + digits[ai+1..];
  if ai < 3 { SeqUpdateSum1(digits, ai, vi_try); }
  else { SeqUpdateSum2(digits, ai, vi_try); }
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
{
  /* code modified by LLM (iteration 5): fix nd_try range proof before calling isLucky */
  var d0 := charToInt(ticket[0]);
  var d1 := charToInt(ticket[1]);
  var d2 := charToInt(ticket[2]);
  var d3 := charToInt(ticket[3]);
  var d4 := charToInt(ticket[4]);
  var d5 := charToInt(ticket[5]);
  var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
  assert digits[0] == d0 && digits[1] == d1 && digits[2] == d2;
  assert digits[3] == d3 && digits[4] == d4 && digits[5] == d5;
  assert forall i :: 0 <= i < 6 ==> 0 <= digits[i] <= 9;
  var sum1 := d0 + d1 + d2;
  var sum2 := d3 + d4 + d5;

  // Check 0 changes
  if sum1 == sum2 {
    result := 0;
    assert isLucky(digits);
    return;
  }

  assert !isLucky(digits);
  assert !canMakeLuckyWith0Changes(digits);

  // Check 1 change
  var can1 := false;
  var p1 := 0;
  var v1 := 0;

  var pos := 0;
  while pos < 6 && !can1
    invariant 0 <= pos <= 6
    invariant can1 ==> (0 <= p1 < 6 && 0 <= v1 <= 9 &&
      (var nd := digits[..p1] + [v1] + digits[p1+1..];
       isLucky(nd)))
    invariant !can1 ==> (forall q :: 0 <= q < pos =>
      forall nv :: 0 <= nv <= 9 =>
        !(var nd := digits[..q] + [nv] + digits[q+1..];
          isLucky(nd)))
  {
    var req: int;
    if pos < 3 {
      req := sum2 - sum1 + digits[pos];
    } else {
      req := sum1 - sum2 + digits[pos];
    }
    if 0 <= req <= 9 {
      can1 := true;
      p1 := pos;
      v1 := req;
      var nd := digits[..p1] + [v1] + digits[p1+1..];
      assert |nd| == 6;
      assert forall i :: 0 <= i < 6 ==> 0 <= nd[i] <= 9;
      if p1 < 3 {
        SeqUpdateSum1(digits, p1, v1);
        assert nd[0] + nd[1] + nd[2] == sum1 - digits[p1] + v1;
        assert nd[3] + nd[4] + nd[5] == sum2;
        assert nd[0] + nd[1] + nd[2] == sum2;
        assert isLucky(nd);
      } else {
        SeqUpdateSum2(digits, p1, v1);
        assert nd[0] + nd[1] + nd[2] == sum1;
        assert nd[3] + nd[4] + nd[5] == sum2 - digits[p1] + v1;
        assert nd[3] + nd[4] + nd[5] == sum1;
        assert isLucky(nd);
      }
    } else {
      assert forall nv :: 0 <= nv <= 9 =>
        !(var nd := digits[..pos] + [nv] + digits[pos+1..];
          isLucky(nd)) by {
        forall nv | 0 <= nv <= 9
          ensures !(var nd := digits[..pos] + [nv] + digits[pos+1..];
                   isLucky(nd))
        {
          var nd := digits[..pos] + [nv] + digits[pos+1..];
          assert |nd| == 6;
          assert forall i :: 0 <= i < 6 ==> 0 <= nd[i] <= 9;
          if pos < 3 {
            SeqUpdateSum1(digits, pos, nv);
            assert nd[0] + nd[1] + nd[2] == sum1 - digits[pos] + nv;
            assert nd[3] + nd[4] + nd[5] == sum2;
            assert nd[0] + nd[1] + nd[2] != nd[3] + nd[4] + nd[5];
          } else {
            SeqUpdateSum2(digits, pos, nv);
            assert nd[0] + nd[1] + nd[2] == sum1;
            assert nd[3] + nd[4] + nd[5] == sum2 - digits[pos] + nv;
            assert nd[0] + nd[1] + nd[2] != nd[3] + nd[4] + nd[5];
          }
        }
      }
    }
    pos := pos + 1;
  }

  if can1 {
    result := 1;
    assert canMakeLuckyWith1Change(digits) by {
      var nd := digits[..p1] + [v1] + digits[p1+1..];
      assert isLucky(nd);
    }
    assert !canMakeLuckyWith0Changes(digits);
    return;
  }

  assert !canMakeLuckyWith1Change(digits) by {
    if canMakeLuckyWith1Change(digits) {
      var pos2 :| 0 <= pos2 < 6 &&
        exists newDigit :: 0 <= newDigit <= 9 &&
          (var nd := digits[..pos2] + [newDigit] + digits[pos2+1..];
           isLucky(nd));
      var newDigit :| 0 <= newDigit <= 9 &&
        (var nd := digits[..pos2] + [newDigit] + digits[pos2+1..];
         isLucky(nd));
      assert !(var nd := digits[..pos2] + [newDigit] + digits[pos2+1..];
               isLucky(nd));
      assert false;
    }
  }

  // Check 2 changes by brute force
  var can2 := false;
  var pi2 := 1; var pj2 := 0; var vi2 := 0; var vj2 := 0;

  var ai := 1;
  while ai < 6 && !can2
    invariant 1 <= ai <= 6
    invariant can2 ==> (0 <= pj2 < pi2 < 6 && 0 <= vi2 <= 9 && 0 <= vj2 <= 9 &&
      (var nd := digits[..pi2] + [vi2] + digits[pi2+1..];
       var fd := nd[..pj2] + [vj2] + nd[pj2+1..];
       isLucky(fd)))
    invariant !can2 ==> (forall a, b :: 1 <= a < ai && 0 <= b < a ==>
      forall kk, ll :: 0 <= kk <= 9 && 0 <= ll <= 9 ==>
        !(var nd := digits[..a] + [kk] + digits[a+1..];
          var fd := nd[..b] + [ll] + nd[b+1..];
          isLucky(fd)))
  {
    var aj := 0;
    while aj < ai && !can2
      invariant 0 <= aj <= ai
      invariant can2 ==> (0 <= pj2 < pi2 < 6 && 0 <= vi2 <= 9 && 0 <= vj2 <= 9 &&
        (var nd := digits[..pi2] + [vi2] + digits[pi2+1..];
         var fd := nd[..pj2] + [vj2] + nd[pj2+1..];
         isLucky(fd)))
      invariant !can2 ==> ((forall a, b :: 1 <= a < ai && 0 <= b < a ==>
          forall kk, ll :: 0 <= kk <= 9 && 0 <= ll <= 9 ==>
            !(var nd := digits[..a] + [kk] + digits[a+1..];
              var fd := nd[..b] + [ll] + nd[b+1..];
              isLucky(fd))) &&
        (forall b :: 0 <= b < aj ==>
          forall kk, ll :: 0 <= kk <= 9 && 0 <= ll <= 9 ==>
            !(var nd := digits[..ai] + [kk] + digits[ai+1..];
              var fd := nd[..b] + [ll] + nd[b+1..];
              isLucky(fd))))
    {
      var vi_try := 0;
      while vi_try <= 9 && !can2
        invariant 0 <= vi_try <= 10
        invariant can2 ==> (0 <= pj2 < pi2 < 6 && 0 <= vi2 <= 9 && 0 <= vj2 <= 9 &&
          (var nd := digits[..pi2] + [vi2] + digits[pi2+1..];
           var fd := nd[..pj2] + [vj2] + nd[pj2+1..];
           isLucky(fd)))
        invariant !can2 ==> ((forall a, b :: 1 <= a < ai && 0 <= b < a ==>
            forall kk, ll :: 0 <= kk <= 9 && 0 <= ll <= 9 ==>
              !(var nd := digits[..a] + [kk] + digits[a+1..];
                var fd := nd[..b] + [ll] + nd[b+1..];
                isLucky(fd))) &&
          (forall b :: 0 <= b < aj ==>
            forall kk, ll :: 0 <= kk <= 9 && 0 <= ll <= 9 ==>
              !(var nd := digits[..ai] + [kk] + digits[ai+1..];
                var fd := nd[..b] + [ll] + nd[b+1..];
                isLucky(fd))) &&
          (forall kk :: 0 <= kk < vi_try ==>
            forall ll :: 0 <= ll <= 9 ==>
              !(var nd := digits[..ai] + [kk] + digits[ai+1..];
                var fd := nd[..aj] + [ll] + nd[aj+1..];
                isLucky(fd))))
      {
        NdInRange(digits, ai, vi_try);
        var nd_try := digits[..ai] + [vi_try] + digits[ai+1..];
        assert |nd_try| == 6;
        assert forall i :: 0 <= i < 6 ==> 0 <= nd_try[i] <= 9;
        var ns1_try := nd_try[0] + nd_try[1] + nd_try[2];
        var ns2_try := nd_try[3] + nd_try[4] + nd_try[5];
        var diff_try := ns1_try - ns2_try;
        var vj_try: int;
        if aj < 3 {
          vj_try := nd_try[aj] - diff_try;
        } else {
          vj_try := nd_try[aj] + diff_try;
        }
        if 0 <= vj_try <= 9 {
          can2 := true;
          pi2 := ai; pj2 := aj; vi2 := vi_try; vj2 := vj_try;
          var nd2 := digits[..pi2] + [vi2] + digits[pi2+1..];
          assert nd2 == nd_try;
          var fd2 := nd2[..pj2] + [vj2] + nd2[pj2+1..];
          assert |nd2| == 6;
          assert forall i :: 0 <= i < 6 ==> 0 <= nd2[i] <= 9;
          assert |fd2| == 6;
          assert forall i :: 0 <= i < 6 ==> 0 <= fd2[i] <= 9 by {
            if aj < 3 { SeqUpdateSum1(nd2, aj, vj_try); }
            else { SeqUpdateSum2(nd2, aj, vj_try); }
          }
          assert isLucky(fd2) by {
            if aj < 3 {
              SeqUpdateSum1(nd2, aj, vj_try);
              assert fd2[0] + fd2[1] + fd2[2] == ns1_try - nd_try[aj] + vj_try;
              assert fd2[3] + fd2[4] + fd2[5] == ns2_try;
              assert vj_try == nd_try[aj] - diff_try;
              assert ns1_try - nd_try[aj] + vj_try == ns2_try;
            } else {
              SeqUpdateSum2(nd2, aj, vj_try);
              assert fd2[0] + fd2[1] + fd2[2] == ns1_try;
              assert fd2[3] + fd2[4] + fd2[5] == ns2_try - nd_try[aj] + vj_try;
              assert vj_try == nd_try[aj] + diff_try;
              assert ns2_try - nd_try[aj] + vj_try == ns1_try;
            }
          }
        } else {
          assert forall ll :: 0 <= ll <= 9 ==>
            !(var nd := digits[..ai] + [vi_try] + digits[ai+1..];
              var fd := nd[..aj] + [ll] + nd[aj+1..];
              isLucky(fd)) by {
            forall ll | 0 <= ll <= 9
              ensures !(var nd := digits[..ai] + [vi_try] + digits[ai+1..];
                        var fd := nd[..aj] + [ll] + nd[aj+1..];
                        isLucky(fd))
            {
              var nd := digits[..ai] + [vi_try] + digits[ai+1..];
              assert nd == nd_try;
              assert forall i :: 0 <= i < 6 ==> 0 <= nd[i] <= 9;
              var fd := nd[..aj] + [ll] + nd[aj+1..];
              assert |nd| == 6;
              assert |fd| == 6;
              if aj < 3 {
                SeqUpdateSum1(nd, aj, ll);
                assert fd[0]+fd[1]+fd[2] == ns1_try - nd_try[aj] + ll;
                assert fd[3]+fd[4]+fd[5] == ns2_try;
                assert fd[0]+fd[1]+fd[2] != fd[3]+fd[4]+fd[5];
              } else {
                SeqUpdateSum2(nd, aj, ll);
                assert fd[0]+fd[1]+fd[2] == ns1_try;
                assert fd[3]+fd[4]+fd[5] == ns2_try - nd_try[aj] + ll;
                assert fd[0]+fd[1]+fd[2] != fd[3]+fd[4]+fd[5];
              }
            }
          }
        }
        vi_try := vi_try + 1;
      }
      aj := aj + 1;
    }
    ai := ai + 1;
  }

  if can2 {
    result := 2;
    assert canMakeLuckyWith2Changes(digits) by {
      var nd := digits[..pi2] + [vi2] + digits[pi2+1..];
      var fd := nd[..pj2] + [vj2] + nd[pj2+1..];
      assert isLucky(fd);
    }
    assert !canMakeLuckyWith0Changes(digits);
    assert !canMakeLuckyWith1Change(digits);
  } else {
    result := 3;
    assert !canMakeLuckyWith0Changes(digits);
    assert !canMakeLuckyWith1Change(digits);
    assert !canMakeLuckyWith2Changes(digits) by {
      if canMakeLuckyWith2Changes(digits) {
        var i2, j2 :| 0 <= j2 < i2 < 6 &&
          exists k2, l2 :: 0 <= k2 <= 9 && 0 <= l2 <= 9 &&
            (var nd2 := digits[..i2] + [k2] + digits[i2+1..];
             var fd2 := nd2[..j2] + [l2] + nd2[j2+1..];
             isLucky(fd2));
        var k2, l2 :| 0 <= k2 <= 9 && 0 <= l2 <= 9 &&
          (var nd2 := digits[..i2] + [k2] + digits[i2+1..];
           var fd2 := nd2[..j2] + [l2] + nd2[j2+1..];
           isLucky(fd2));
        NdInRange(digits, i2, k2);
        var nd2 := digits[..i2] + [k2] + digits[i2+1..];
        var fd2 := nd2[..j2] + [l2] + nd2[j2+1..];
        var ns1_2 := nd2[0] + nd2[1] + nd2[2];
        var ns2_2 := nd2[3] + nd2[4] + nd2[5];
        var diff2v := ns1_2 - ns2_2;
        var vj_c: int;
        if j2 < 3 {
          vj_c := nd2[j2] - diff2v;
          SeqUpdateSum1(nd2, j2, l2);
          assert fd2[0]+fd2[1]+fd2[2] == ns1_2 - nd2[j2] + l2;
          assert fd2[3]+fd2[4]+fd2[5] == ns2_2;
          assert ns1_2 - nd2[j2] + l2 == ns2_2;
          assert l2 == nd2[j2] - diff2v;
          assert l2 == vj_c;
        } else {
          vj_c := nd2[j2] + diff2v;
          SeqUpdateSum2(nd2, j2, l2);
          assert fd2[0]+fd2[1]+fd2[2] == ns1_2;
          assert fd2[3]+fd2[4]+fd2[5] == ns2_2 - nd2[j2] + l2;
          assert ns1_2 == ns2_2 - nd2[j2] + l2;
          assert l2 == diff2v + nd2[j2];
          assert l2 == vj_c;
        }
        assert 0 <= vj_c <= 9;
        assert !can2;
        assert false;
      }
    }
  }
}
// </vc-code>
