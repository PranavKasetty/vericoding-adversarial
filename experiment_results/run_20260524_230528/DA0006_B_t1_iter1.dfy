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
lemma CanAlwaysMakeIn3Changes(digits: seq<int>)
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures canMakeLuckyWith2Changes(digits)
{
  var diff := (digits[0] + digits[1] + digits[2]) - (digits[3] + digits[4] + digits[5]);
  if diff == 0 {
    var newDigits := digits[..0] + [digits[0]] + digits[1..];
    var finalDigits := newDigits[..3] + [digits[3]] + newDigits[4..];
    assert isLucky(finalDigits);
  } else if diff > 0 {
    var adj := if diff <= 9 - digits[0] then diff else 9 - digits[0];
    var newDigits := digits[..0] + [digits[0] + adj] + digits[1..];
    var remaining := diff - adj;
    var adj2 := remaining;
    if digits[3] >= adj2 {
      var finalDigits := newDigits[..3] + [digits[3] - adj2] + newDigits[4..];
      assert isLucky(finalDigits);
    } else {
      var adj1b := diff - (digits[3]);
      var newDigits2 := digits[..0] + [digits[0] + adj1b] + digits[1..];
      var finalDigits2 := newDigits2[..3] + [0] + newDigits2[4..];
      assert isLucky(finalDigits2);
    }
  } else {
    var absdiff := -diff;
    var adj := if absdiff <= digits[0] then absdiff else digits[0];
    var newDigits := digits[..0] + [digits[0] - adj] + digits[1..];
    var remaining := absdiff - adj;
    if digits[3] + remaining <= 9 {
      var finalDigits := newDigits[..3] + [digits[3] + remaining] + newDigits[4..];
      assert isLucky(finalDigits);
    } else {
      var adj1b := absdiff - (9 - digits[3]);
      var newDigits2 := digits[..0] + [digits[0] - adj1b] + digits[1..];
      var finalDigits2 := newDigits2[..3] + [9] + newDigits2[4..];
      assert isLucky(finalDigits2);
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
{
  var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
  var sum1 := digits[0] + digits[1] + digits[2];
  var sum2 := digits[3] + digits[4] + digits[5];
  var diff := sum1 - sum2;
  if diff == 0 {
    result := 0;
  } else {
    // Check if 1 change suffices
    var can1 := false;
    var pos := 0;
    while pos < 6
      invariant 0 <= pos <= 6
      invariant !can1 ==> forall p :: 0 <= p < pos ==> forall nd :: 0 <= nd <= 9 ==> !isLucky(digits[..p] + [nd] + digits[p+1..])
    {
      var nd := 0;
      while nd <= 9
        invariant 0 <= nd <= 10
        invariant !can1 ==> forall nd2 :: 0 <= nd2 < nd ==> !isLucky(digits[..pos] + [nd2] + digits[pos+1..])
      {
        var newDigits := digits[..pos] + [nd] + digits[pos+1..];
        if isLucky(newDigits) {
          can1 := true;
        }
        nd := nd + 1;
      }
      pos := pos + 1;
    }
    if can1 {
      result := 1;
    } else {
      CanAlwaysMakeIn3Changes(digits);
      // Check if 2 changes suffice
      var can2 := false;
      var i := 1;
      while i < 6
        invariant 1 <= i <= 6
        invariant !can2 ==> forall i2, j2 :: 0 <= j2 < i2 < i ==> forall k :: 0 <= k <= 9 ==> forall l :: 0 <= l <= 9 ==> var nd := digits[..i2] + [k] + digits[i2+1..]; !isLucky(nd[..j2] + [l] + nd[j2+1..])
      {
        var j := 0;
        while j < i
          invariant 0 <= j <= i
          invariant !can2 ==> forall j2 :: 0 <= j2 < j ==> forall k :: 0 <= k <= 9 ==> forall l :: 0 <= l <= 9 ==> var nd := digits[..i] + [k] + digits[i+1..]; !isLucky(nd[..j2] + [l] + nd[j2+1..])
        {
          var k := 0;
          while k <= 9
            invariant 0 <= k <= 10
          {
            var l := 0;
            while l <= 9
              invariant 0 <= l <= 10
            {
              var nd := digits[..i] + [k] + digits[i+1..];
              var fd := nd[..j] + [l] + nd[j+1..];
              if isLucky(fd) {
                can2 := true;
              }
              l := l + 1;
            }
            k := k + 1;
          }
          j := j + 1;
        }
        i := i + 1;
      }
      if can2 {
        result := 2;
      } else {
        result := 3;
      }
    }
  }
}
// </vc-code>
