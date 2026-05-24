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
/* helper modified by LLM (iteration 3): helper lemmas for lucky change proofs */
lemma CanMake1ChangeFromPos(digits: seq<int>, pos: int, newDigit: int)
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  requires 0 <= pos < 6
  requires 0 <= newDigit <= 9
  requires var newDigits := digits[..pos] + [newDigit] + digits[pos+1..];
           isLucky(newDigits)
  ensures canMakeLuckyWith1Change(digits)
{
  var newDigits := digits[..pos] + [newDigit] + digits[pos+1..];
  assert isLucky(newDigits);
}

lemma CanMake2ChangesFromPos(digits: seq<int>, ii: int, jj: int, kk: int, ll: int)
  requires |digits| == 6
  requires forall idx :: 0 <= idx < |digits| ==> 0 <= digits[idx] <= 9
  requires 0 <= jj < ii < 6
  requires 0 <= kk <= 9 && 0 <= ll <= 9
  requires var newDigits := digits[..ii] + [kk] + digits[ii+1..];
           var finalDigits := newDigits[..jj] + [ll] + newDigits[jj+1..];
           isLucky(finalDigits)
  ensures canMakeLuckyWith2Changes(digits)
{
  var newDigits := digits[..ii] + [kk] + digits[ii+1..];
  var finalDigits := newDigits[..jj] + [ll] + newDigits[jj+1..];
  assert isLucky(finalDigits);
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
  /* code modified by LLM (iteration 3): full exhaustive search with complete invariants */
  var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
  var sum1 := digits[0] + digits[1] + digits[2];
  var sum2 := digits[3] + digits[4] + digits[5];
  if sum1 == sum2 {
    result := 0;
  } else {
    // Check 1 change
    var can1 := false;
    var p1 := 0;
    var nd1 := 0;
    var pos := 0;
    while pos < 6
      invariant 0 <= pos <= 6
      invariant (can1 ==> (0 <= p1 < pos && 0 <= nd1 <= 9 &&
        (var nd := digits[..p1] + [nd1] + digits[p1+1..]; isLucky(nd))))
      invariant (!can1 ==> (forall p, nd :: (0 <= p < pos && 0 <= nd <= 9) ==> !(var nds := digits[..p] + [nd] + digits[p+1..]; isLucky(nds))))
    {
      if !can1 {
        var needed: int;
        if pos < 3 {
          needed := sum2 - (sum1 - digits[pos]);
        } else {
          needed := sum1 - (sum2 - digits[pos]);
        }
        if 0 <= needed <= 9 {
          can1 := true;
          p1 := pos;
          nd1 := needed;
        }
      }
      pos := pos + 1;
    }
    if can1 {
      var newDigits := digits[..p1] + [nd1] + digits[p1+1..];
      assert isLucky(newDigits);
      CanMake1ChangeFromPos(digits, p1, nd1);
      result := 1;
    } else {
      assert !canMakeLuckyWith1Change(digits);
      // Check 2 changes: try all pairs (i,j) with 0<=j<i<6 and all k,l in 0..9
      var can2 := false;
      var i2 := 1;
      var j2 := 0;
      var k2 := 0;
      var l2 := 0;
      var ii := 1;
      while ii < 6
        invariant 1 <= ii <= 6
        invariant (can2 ==> (0 <= j2 < i2 < 6 && 0 <= k2 <= 9 && 0 <= l2 <= 9 &&
          (var nd := digits[..i2] + [k2] + digits[i2+1..]; var fd := nd[..j2] + [l2] + nd[j2+1..]; isLucky(fd))))
        invariant (!can2 ==> (forall a, b, k, l :: (1 <= a < ii && 0 <= b < a && 0 <= k <= 9 && 0 <= l <= 9) ==>
          !(var nd := digits[..a] + [k] + digits[a+1..]; var fd := nd[..b] + [l] + nd[b+1..]; isLucky(fd))))
      {
        var jj := 0;
        while jj < ii
          invariant 0 <= jj <= ii
          invariant (can2 ==> (0 <= j2 < i2 < 6 && 0 <= k2 <= 9 && 0 <= l2 <= 9 &&
            (var nd := digits[..i2] + [k2] + digits[i2+1..]; var fd := nd[..j2] + [l2] + nd[j2+1..]; isLucky(fd))))
          invariant (!can2 ==> (forall a, b, k, l :: (1 <= a < ii && 0 <= b < a && 0 <= k <= 9 && 0 <= l <= 9) ==>
            !(var nd := digits[..a] + [k] + digits[a+1..]; var fd := nd[..b] + [l] + nd[b+1..]; isLucky(fd))))
          invariant (!can2 ==> (forall b, k, l :: (0 <= b < jj && 0 <= k <= 9 && 0 <= l <= 9) ==>
            !(var nd := digits[..ii] + [k] + digits[ii+1..]; var fd := nd[..b] + [l] + nd[b+1..]; isLucky(fd))))
        {
          var kk := 0;
          while kk <= 9
            invariant 0 <= kk <= 10
            invariant (can2 ==> (0 <= j2 < i2 < 6 && 0 <= k2 <= 9 && 0 <= l2 <= 9 &&
              (var nd := digits[..i2] + [k2] + digits[i2+1..]; var fd := nd[..j2] + [l2] + nd[j2+1..]; isLucky(fd))))
            invariant (!can2 ==> (forall a, b, k, l :: (1 <= a < ii && 0 <= b < a && 0 <= k <= 9 && 0 <= l <= 9) ==>
              !(var nd := digits[..a] + [k] + digits[a+1..]; var fd := nd[..b] + [l] + nd[b+1..]; isLucky(fd))))
            invariant (!can2 ==> (forall b, k, l :: (0 <= b < jj && 0 <= k <= 9 && 0 <= l <= 9) ==>
              !(var nd := digits[..ii] + [k] + digits[ii+1..]; var fd := nd[..b] + [l] + nd[b+1..]; isLucky(fd))))
            invariant (!can2 ==> (forall l :: 0 <= l <= 9 ==>
              !(var nd := digits[..ii] + [kk] + digits[ii+1..]; var fd := nd[..jj] + [l] + nd[jj+1..]; isLucky(fd))))
          {
            var newDigits := digits[..ii] + [kk] + digits[ii+1..];
            var ns1 := newDigits[0] + newDigits[1] + newDigits[2];
            var ns2 := newDigits[3] + newDigits[4] + newDigits[5];
            var needed: int;
            if jj < 3 {
              needed := ns2 - (ns1 - newDigits[jj]);
            } else {
              needed := ns1 - (ns2 - newDigits[jj]);
            }
            if 0 <= needed <= 9 {
              can2 := true;
              i2 := ii; j2 := jj; k2 := kk; l2 := needed;
            }
            kk := kk + 1;
          }
          jj := jj + 1;
        }
        ii := ii + 1;
      }
      if can2 {
        var newDigits := digits[..i2] + [k2] + digits[i2+1..];
        var finalDigits := newDigits[..j2] + [l2] + newDigits[j2+1..];
        assert isLucky(finalDigits);
        CanMake2ChangesFromPos(digits, i2, j2, k2, l2);
        result := 2;
      } else {
        result := 3;
      }
    }
  }
}
// </vc-code>
