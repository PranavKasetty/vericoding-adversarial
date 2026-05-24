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
/* helper modified by LLM (iteration 2): simplified lemma to prove canMakeLuckyWith1Change */
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

lemma CanMake2ChangesFromPos(digits: seq<int>, i: int, j: int, k: int, l: int)
  requires |digits| == 6
  requires forall idx :: 0 <= idx < |digits| ==> 0 <= digits[idx] <= 9
  requires 0 <= j < i < 6
  requires 0 <= k <= 9 && 0 <= l <= 9
  requires var newDigits := digits[..i] + [k] + digits[i+1..];
           var finalDigits := newDigits[..j] + [l] + newDigits[j+1..];
           isLucky(finalDigits)
  ensures canMakeLuckyWith2Changes(digits)
{
  var newDigits := digits[..i] + [k] + digits[i+1..];
  var finalDigits := newDigits[..j] + [l] + newDigits[j+1..];
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
  /* code modified by LLM (iteration 2): complete implementation without var :| parse issues */
  var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
  var sum1 := digits[0] + digits[1] + digits[2];
  var sum2 := digits[3] + digits[4] + digits[5];
  if sum1 == sum2 {
    result := 0;
  } else {
    // Check if 1 change suffices
    var can1 := false;
    var p1 := -1;
    var nd1 := -1;
    var pos := 0;
    while pos < 6
      invariant 0 <= pos <= 6
      invariant can1 ==> 0 <= p1 < pos && 0 <= nd1 <= 9 &&
        (var nd := digits[..p1] + [nd1] + digits[p1+1..]; isLucky(nd))
      invariant !can1 ==> forall p :: 0 <= p < pos ==> forall nd :: 0 <= nd <= 9 ==> !(var nds := digits[..p] + [nd] + digits[p+1..]; isLucky(nds))
    {
      if !can1 {
        if pos < 3 {
          var needed := sum2 - (sum1 - digits[pos]);
          if 0 <= needed <= 9 {
            can1 := true;
            p1 := pos;
            nd1 := needed;
          }
        } else {
          var needed := sum1 - (sum2 - digits[pos]);
          if 0 <= needed <= 9 {
            can1 := true;
            p1 := pos;
            nd1 := needed;
          }
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
      // Check if 2 changes suffice
      var can2 := false;
      var i2 := -1;
      var j2 := -1;
      var k2 := -1;
      var l2 := -1;
      var i := 1;
      while i < 6 && !can2
        invariant 1 <= i <= 6
        invariant can2 ==> 0 <= j2 < i2 < 6 && 0 <= k2 <= 9 && 0 <= l2 <= 9 &&
          (var nd := digits[..i2] + [k2] + digits[i2+1..]; var fd := nd[..j2] + [l2] + nd[j2+1..]; isLucky(fd))
      {
        var j := 0;
        while j < i && !can2
          invariant 0 <= j <= i
          invariant can2 ==> 0 <= j2 < i2 < 6 && 0 <= k2 <= 9 && 0 <= l2 <= 9 &&
            (var nd := digits[..i2] + [k2] + digits[i2+1..]; var fd := nd[..j2] + [l2] + nd[j2+1..]; isLucky(fd))
        {
          var k := 0;
          while k <= 9 && !can2
            invariant 0 <= k <= 10
            invariant can2 ==> 0 <= j2 < i2 < 6 && 0 <= k2 <= 9 && 0 <= l2 <= 9 &&
              (var nd := digits[..i2] + [k2] + digits[i2+1..]; var fd := nd[..j2] + [l2] + nd[j2+1..]; isLucky(fd))
          {
            var newDigits := digits[..i] + [k] + digits[i+1..];
            // After changing position i to k, need position j to make sums equal
            // newDigits sum1 and sum2 depend on positions
            var ns1 := newDigits[0] + newDigits[1] + newDigits[2];
            var ns2 := newDigits[3] + newDigits[4] + newDigits[5];
            if j < 3 {
              var needed := ns2 - (ns1 - newDigits[j]);
              if 0 <= needed <= 9 {
                can2 := true;
                i2 := i; j2 := j; k2 := k; l2 := needed;
              }
            } else {
              var needed := ns1 - (ns2 - newDigits[j]);
              if 0 <= needed <= 9 {
                can2 := true;
                i2 := i; j2 := j; k2 := k; l2 := needed;
              }
            }
            k := k + 1;
          }
          j := j + 1;
        }
        i := i + 1;
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
