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
/* helper modified by LLM (iteration 3): removed incorrect characterization lemma, provide helpers for direct computation */
lemma CanMake1ChangeWitness(digits: seq<int>, pos: int, newDigit: int)
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  requires 0 <= pos < 6
  requires 0 <= newDigit <= 9
  requires isLucky(digits[..pos] + [newDigit] + digits[pos+1..])
  ensures canMakeLuckyWith1Change(digits)
{
  assert exists p :: 0 <= p < 6 && exists nd :: 0 <= nd <= 9 && isLucky(digits[..p] + [nd] + digits[p+1..]);
}

lemma CanMake2ChangeWitness(digits: seq<int>, i: int, j: int, k: int, l: int)
  requires |digits| == 6
  requires forall idx :: 0 <= idx < |digits| ==> 0 <= digits[idx] <= 9
  requires 0 <= j < i < 6
  requires 0 <= k <= 9
  requires 0 <= l <= 9
  requires var newDigits := digits[..i] + [k] + digits[i+1..];
           var finalDigits := newDigits[..j] + [l] + newDigits[j+1..];
           isLucky(finalDigits)
  ensures canMakeLuckyWith2Changes(digits)
{
  assert exists ii, jj :: 0 <= jj < ii < 6 && exists kk, ll :: 0 <= kk <= 9 && 0 <= ll <= 9 &&
    var nd := digits[..ii] + [kk] + digits[ii+1..];
    var fd := nd[..jj] + [ll] + nd[jj+1..];
    isLucky(fd);
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
  /* code modified by LLM (iteration 3): brute force compute canMakeLucky by trying all changes */
  var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
  var s1 := digits[0] + digits[1] + digits[2];
  var s2 := digits[3] + digits[4] + digits[5];

  if s1 == s2 {
    result := 0;
    return;
  }

  // Check if 1 change suffices: try all positions and all newDigit values
  var can1 := false;
  var p1 := 0;
  while p1 < 6
    invariant 0 <= p1 <= 6
    invariant can1 ==> canMakeLuckyWith1Change(digits)
  {
    var nd := 0;
    while nd <= 9
      invariant 0 <= nd <= 10
      invariant can1 ==> canMakeLuckyWith1Change(digits)
    {
      var newDigits := digits[..p1] + [nd] + digits[p1+1..];
      if isLucky(newDigits) {
        CanMake1ChangeWitness(digits, p1, nd);
        can1 := true;
      }
      nd := nd + 1;
    }
    p1 := p1 + 1;
  }

  if can1 {
    result := 1;
    // Need to show !canMakeLuckyWith0Changes
    assert !isLucky(digits);
    return;
  }

  // Check if 2 changes suffice
  var can2 := false;
  var i2 := 1;
  while i2 < 6
    invariant 1 <= i2 <= 6
    invariant can2 ==> canMakeLuckyWith2Changes(digits)
  {
    var j2 := 0;
    while j2 < i2
      invariant 0 <= j2 <= i2
      invariant can2 ==> canMakeLuckyWith2Changes(digits)
    {
      var k2 := 0;
      while k2 <= 9
        invariant 0 <= k2 <= 10
        invariant can2 ==> canMakeLuckyWith2Changes(digits)
      {
        var l2 := 0;
        while l2 <= 9
          invariant 0 <= l2 <= 10
          invariant can2 ==> canMakeLuckyWith2Changes(digits)
        {
          var newDigits := digits[..i2] + [k2] + digits[i2+1..];
          var finalDigits := newDigits[..j2] + [l2] + newDigits[j2+1..];
          if isLucky(finalDigits) {
            CanMake2ChangeWitness(digits, i2, j2, k2, l2);
            can2 := true;
          }
          l2 := l2 + 1;
        }
        k2 := k2 + 1;
      }
      j2 := j2 + 1;
    }
    i2 := i2 + 1;
  }

  if can2 {
    result := 2;
    assert !isLucky(digits);
    assert !canMakeLuckyWith1Change(digits);
    return;
  }

  result := 3;
  assert !isLucky(digits);
  assert !canMakeLuckyWith1Change(digits);
  assert !canMakeLuckyWith2Changes(digits);
}
// </vc-code>
