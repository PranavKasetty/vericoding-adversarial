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
  var diff := if sum1 >= sum2 then sum1 - sum2 else sum2 - sum1;
  
  if diff == 0 {
    result := 0;
  } else if diff <= 9 {
    result := 1;
    // Witness for canMakeLuckyWith1Change
    if sum1 > sum2 {
      // Change digits[0] by -diff if possible, else find position
      if digits[0] >= diff {
        var newDigit := digits[0] - diff;
        assert 0 <= newDigit <= 9;
        var newDigits := digits[..0] + [newDigit] + digits[1..];
        assert isLucky(newDigits);
      } else if digits[1] >= diff {
        var newDigit := digits[1] - diff;
        var newDigits := digits[..1] + [newDigit] + digits[2..];
        assert isLucky(newDigits);
      } else {
        var newDigit := digits[2] - diff;
        var newDigits := digits[..2] + [newDigit] + digits[3..];
        assert isLucky(newDigits);
      }
    } else {
      if digits[3] >= diff {
        var newDigit := digits[3] - diff;
        var newDigits := digits[..3] + [newDigit] + digits[4..];
        assert isLucky(newDigits);
      } else if digits[4] >= diff {
        var newDigit := digits[4] - diff;
        var newDigits := digits[..4] + [newDigit] + digits[5..];
        assert isLucky(newDigits);
      } else {
        var newDigit := digits[5] - diff;
        var newDigits := digits[..5] + [newDigit] + digits[6..];
        assert isLucky(newDigits);
      }
    }
  } else if diff <= 18 {
    result := 2;
  } else {
    result := 3;
  }
}
// </vc-code>
