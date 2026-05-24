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
/* helper modified by LLM (iteration 5): simplified witness and bounds lemmas */
lemma NewDigitsBounds(digits: seq<int>, pos: int, nd: int)
  requires |digits| == 6
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  requires 0 <= pos < 6
  requires 0 <= nd <= 9
  ensures var newDigits := digits[..pos] + [nd] + digits[pos+1..];
          |newDigits| == 6 && forall i :: 0 <= i < |newDigits| ==> 0 <= newDigits[i] <= 9
{
  var newDigits := digits[..pos] + [nd] + digits[pos+1..];
  assert |newDigits| == 6;
  forall i | 0 <= i < 6 ensures 0 <= newDigits[i] <= 9 {
    if i < pos {
      assert newDigits[i] == digits[i];
    } else if i == pos {
      assert newDigits[i] == nd;
    } else {
      assert newDigits[i] == digits[i];
    }
  }
}

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
  assert exists ii, jj :: 0 <= jj < ii < 6 && (exists kk, ll :: 0 <= kk <= 9 && 0 <= ll <= 9 &&
    (var nd := digits[..ii] + [kk] + digits[ii+1..];
    var fd := nd[..jj] + [ll] + nd[jj+1..];
    isLucky(fd)));
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
  /* code modified by LLM (iteration 5): use arithmetic shortcut to avoid timeout */
  var digits := seq(6, i requires 0 <= i < 6 => charToInt(ticket[i]));
  assert forall i :: 0 <= i < 6 ==> 0 <= digits[i] <= 9;
  var s1 := digits[0] + digits[1] + digits[2];
  var s2 := digits[3] + digits[4] + digits[5];

  if s1 == s2 {
    result := 0;
    return;
  }

  // Check 1 change
  var can1 := false;
  var p1 := 0;
  while p1 < 6
    invariant 0 <= p1 <= 6
    invariant can1 ==> canMakeLuckyWith1Change(digits)
    invariant !can1 ==> forall p :: 0 <= p < p1 ==> forall nd :: 0 <= nd <= 9 ==> !isLucky(digits[..p] + [nd] + digits[p+1..])
  {
    var nd := 0;
    while nd <= 9
      invariant 0 <= nd <= 10
      invariant can1 ==> canMakeLuckyWith1Change(digits)
      invariant !can1 ==> forall p :: 0 <= p < p1 ==> forall nd2 :: 0 <= nd2 <= 9 ==> !isLucky(digits[..p] + [nd2] + digits[p+1..])
      invariant !can1 ==> forall nd2 :: 0 <= nd2 < nd ==> !isLucky(digits[..p1] + [nd2] + digits[p1+1..])
    {
      NewDigitsBounds(digits, p1, nd);
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
    assert !isLucky(digits);
    assert !canMakeLuckyWith0Changes(digits);
    return;
  }

  assert !canMakeLuckyWith1Change(digits) by {
    if canMakeLuckyWith1Change(digits) {
      var p :| 0 <= p < 6 && exists nd :: 0 <= nd <= 9 && isLucky(digits[..p] + [nd] + digits[p+1..]);
      var nd :| 0 <= nd <= 9 && isLucky(digits[..p] + [nd] + digits[p+1..]);
      assert false;
    }
  }

  // Check 2 changes using arithmetic: max adjustment per change is 9
  // With 2 changes we can adjust sum difference by at most 18
  var diff := if s1 > s2 then s1 - s2 else s2 - s1;
  if diff <= 18 {
    // Find witness
    var i2 := 1;
    var found2 := false;
    while i2 < 6 && !found2
      invariant 1 <= i2 <= 6
      invariant found2 ==> canMakeLuckyWith2Changes(digits)
    {
      var j2 := 0;
      while j2 < i2 && !found2
        invariant 0 <= j2 <= i2
        invariant found2 ==> canMakeLuckyWith2Changes(digits)
      {
        var k2 := 0;
        while k2 <= 9 && !found2
          invariant 0 <= k2 <= 10
          invariant found2 ==> canMakeLuckyWith2Changes(digits)
        {
          NewDigitsBounds(digits, i2, k2);
          var newDigits := digits[..i2] + [k2] + digits[i2+1..];
          var l2 := 0;
          while l2 <= 9 && !found2
            invariant 0 <= l2 <= 10
            invariant found2 ==> canMakeLuckyWith2Changes(digits)
          {
            NewDigitsBounds(newDigits, j2, l2);
            var finalDigits := newDigits[..j2] + [l2] + newDigits[j2+1..];
            if isLucky(finalDigits) {
              CanMake2ChangeWitness(digits, i2, j2, k2, l2);
              found2 := true;
            }
            l2 := l2 + 1;
          }
          k2 := k2 + 1;
        }
        j2 := j2 + 1;
      }
      i2 := i2 + 1;
    }
    if found2 {
      result := 2;
      return;
    }
  }

  // Verify can2 is false by exhaustive check
  var notCan2 := true;
  var ci := 1;
  while ci < 6
    invariant 1 <= ci <= 6
    invariant !notCan2 ==> canMakeLuckyWith2Changes(digits)
  {
    var cj := 0;
    while cj < ci
      invariant 0 <= cj <= ci
      invariant !notCan2 ==> canMakeLuckyWith2Changes(digits)
    {
      var ck := 0;
      while ck <= 9
        invariant 0 <= ck <= 10
        invariant !notCan2 ==> canMakeLuckyWith2Changes(digits)
      {
        NewDigitsBounds(digits, ci, ck);
        var nd2 := digits[..ci] + [ck] + digits[ci+1..];
        var cl := 0;
        while cl <= 9
          invariant 0 <= cl <= 10
          invariant !notCan2 ==> canMakeLuckyWith2Changes(digits)
        {
          NewDigitsBounds(nd2, cj, cl);
          var fd2 := nd2[..cj] + [cl] + nd2[cj+1..];
          if isLucky(fd2) {
            CanMake2ChangeWitness(digits, ci, cj, ck, cl);
            notCan2 := false;
          }
          cl := cl + 1;
        }
        ck := ck + 1;
      }
      cj := cj + 1;
    }
    ci := ci + 1;
  }

  if !notCan2 {
    result := 2;
    return;
  }

  assert !canMakeLuckyWith2Changes(digits) by {
    if canMakeLuckyWith2Changes(digits) {
      var ii, jj :| (0 <= jj < ii < 6) && (exists kk, ll :: 0 <= kk <= 9 && 0 <= ll <= 9 &&
        (var nd := digits[..ii] + [kk] + digits[ii+1..];
        var fd := nd[..jj] + [ll] + nd[jj+1..];
        isLucky(fd)));
      var kk, ll :| 0 <= kk <= 9 && 0 <= ll <= 9 &&
        (var nd := digits[..ii] + [kk] + digits[ii+1..];
        var fd := nd[..jj] + [ll] + nd[jj+1..];
        isLucky(fd));
      assert false;
    }
  }

  result := 3;
}
// </vc-code>
