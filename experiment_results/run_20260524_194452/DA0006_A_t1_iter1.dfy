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
lemma CanMake1Change(digits: seq<int>, sum1: int, sum2: int)
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  requires sum1 == digits[0] + digits[1] + digits[2]
  requires sum2 == digits[3] + digits[4] + digits[5]
  requires !isLucky(digits)
  requires (exists pos :: 0 <= pos < 3 && 0 <= sum2 - (sum1 - digits[pos]) <= 9) ||
           (exists pos :: 3 <= pos < 6 && 0 <= sum1 - (sum2 - digits[pos]) <= 9)
  ensures canMakeLuckyWith1Change(digits)
{
  if exists pos :: 0 <= pos < 3 && 0 <= sum2 - (sum1 - digits[pos]) <= 9 {
    var pos :| 0 <= pos < 3 && 0 <= sum2 - (sum1 - digits[pos]) <= 9;
    var newDigit := sum2 - (sum1 - digits[pos]);
    var newDigits := digits[..pos] + [newDigit] + digits[pos+1..];
    assert |newDigits| == 6;
    assert forall i :: 0 <= i < 6 ==> 0 <= newDigits[i] <= 9;
    assert newDigits[0] + newDigits[1] + newDigits[2] == sum2;
    assert newDigits[3] + newDigits[4] + newDigits[5] == sum2;
    assert isLucky(newDigits);
  } else {
    var pos :| 3 <= pos < 6 && 0 <= sum1 - (sum2 - digits[pos]) <= 9;
    var newDigit := sum1 - (sum2 - digits[pos]);
    var newDigits := digits[..pos] + [newDigit] + digits[pos+1..];
    assert |newDigits| == 6;
    assert forall i :: 0 <= i < 6 ==> 0 <= newDigits[i] <= 9;
    assert newDigits[0] + newDigits[1] + newDigits[2] == sum1;
    assert newDigits[3] + newDigits[4] + newDigits[5] == sum1;
    assert isLucky(newDigits);
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
  if sum1 == sum2 {
    result := 0;
  } else {
    var can1 := false;
    var pos := 0;
    while pos < 6
      invariant 0 <= pos <= 6
      invariant can1 <==> exists p :: 0 <= p < pos &&
        ((p < 3 && 0 <= sum2 - (sum1 - digits[p]) <= 9) ||
         (p >= 3 && 0 <= sum1 - (sum2 - digits[p]) <= 9))
    {
      if pos < 3 && 0 <= sum2 - (sum1 - digits[pos]) <= 9 {
        can1 := true;
      } else if pos >= 3 && 0 <= sum1 - (sum2 - digits[pos]) <= 9 {
        can1 := true;
      }
      pos := pos + 1;
    }
    if can1 {
      var witness :| 0 <= witness < 6 &&
        ((witness < 3 && 0 <= sum2 - (sum1 - digits[witness]) <= 9) ||
         (witness >= 3 && 0 <= sum1 - (sum2 - digits[witness]) <= 9));
      CanMake1Change(digits, sum1, sum2);
      result := 1;
    } else {
      result := 2;
    }
  }
}
// </vc-code>
