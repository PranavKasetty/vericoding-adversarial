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
lemma LuckyCharacterization(digits: seq<int>)
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures var diff := (digits[0]+digits[1]+digits[2]) - (digits[3]+digits[4]+digits[5]);
    canMakeLuckyWith0Changes(digits) <==> diff == 0
  ensures var diff := (digits[0]+digits[1]+digits[2]) - (digits[3]+digits[4]+digits[5]);
    canMakeLuckyWith1Change(digits) <==> (diff != 0 && -9 <= diff <= 9)
  ensures var diff := (digits[0]+digits[1]+digits[2]) - (digits[3]+digits[4]+digits[5]);
    canMakeLuckyWith2Changes(digits) <==> ((diff < -9 || diff > 9) && -18 <= diff <= 18)
{
  var s1 := digits[0]+digits[1]+digits[2];
  var s2 := digits[3]+digits[4]+digits[5];
  var diff := s1 - s2;
  if diff != 0 && -9 <= diff <= 9 {
    if diff > 0 {
      var pos := 5;
      var newDigit := digits[5] + diff;
      if newDigit <= 9 {
        var newDigits := digits[..pos] + [newDigit] + digits[pos+1..];
        assert isLucky(newDigits);
      } else {
        var pos2 := 0;
        var newDigit2 := digits[0] - diff;
        if newDigit2 >= 0 {
          var newDigits2 := digits[..pos2] + [newDigit2] + digits[pos2+1..];
          assert isLucky(newDigits2);
        } else {
          var sub := digits[5];
          var add := diff - sub;
          var nd5 := 0;
          var nd2 := digits[2] - add;
          var nd := digits[..5] + [nd5] + digits[6..];
          var nd2s := nd[..2] + [nd2] + nd[3..];
          assert isLucky(nd2s);
        }
      }
    } else {
      var d := -diff;
      var pos := 5;
      var newDigit := digits[5] - d;
      if newDigit >= 0 {
        var newDigits := digits[..pos] + [newDigit] + digits[pos+1..];
        assert isLucky(newDigits);
      } else {
        var pos2 := 0;
        var newDigit2 := digits[0] + d;
        if newDigit2 <= 9 {
          var newDigits2 := digits[..pos2] + [newDigit2] + digits[pos2+1..];
          assert isLucky(newDigits2);
        } else {
          var add := 9 - digits[5];
          var nd5 := 9;
          var nd := digits[..5] + [nd5] + digits[6..];
          var rem := d - add;
          var nd2 := digits[2] + rem;
          var nd2s := nd[..2] + [nd2] + nd[3..];
          assert isLucky(nd2s);
        }
      }
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
  LuckyCharacterization(digits);
  if diff == 0 {
    result := 0;
  } else if -9 <= diff <= 9 {
    result := 1;
  } else if -18 <= diff <= 18 {
    result := 2;
  } else {
    result := 3;
  }
}
// </vc-code>
