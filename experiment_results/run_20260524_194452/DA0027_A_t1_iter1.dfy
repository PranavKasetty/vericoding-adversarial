// <vc-preamble>
predicate ValidInputString(s: string)
{
    |s| >= 7 &&
    ContainsFourLines(s) &&
    AllLinesHaveFourValidIntegers(s)
}

predicate ContainsFourLines(s: string)
{
    CountNewlines(s, 0) >= 3
}

predicate AllLinesHaveFourValidIntegers(s: string)
{
    forall i :: 0 <= i < |s| ==> (s[i] == '0' || s[i] == '1' || s[i] == ' ' || s[i] == '\n')
}

predicate ParseInput(s: string, input_lines: seq<seq<int>>)
{
    |input_lines| == 4 &&
    (forall i :: 0 <= i < 4 ==> |input_lines[i]| == 4) &&
    (forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> 
        (input_lines[i][j] >= 0 && input_lines[i][j] <= 1)) &&
    StringContainsFourLinesOfFourIntegers(s, input_lines)
}

predicate StringContainsFourLinesOfFourIntegers(s: string, input_lines: seq<seq<int>>)
{
    |input_lines| == 4 &&
    (forall i :: 0 <= i < 4 ==> |input_lines[i]| == 4) &&
    ValidInputString(s)
}

predicate AccidentPossible(lanes: seq<seq<int>>)
    requires |lanes| == 4
    requires forall i :: 0 <= i < 4 ==> |lanes[i]| == 4
    requires forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> 
        (lanes[i][j] == 0 || lanes[i][j] == 1)
{
    exists i :: 0 <= i < 4 && AccidentAtLane(i, lanes)
}

predicate AccidentAtLane(i: int, lanes: seq<seq<int>>)
    requires 0 <= i < 4
    requires |lanes| == 4
    requires forall j :: 0 <= j < 4 ==> |lanes[j]| == 4
{
    (lanes[i][3] == 1 && (lanes[i][0] == 1 || lanes[i][1] == 1 || lanes[i][2] == 1)) ||
    (lanes[i][0] == 1 && lanes[(i + 3) % 4][3] == 1) ||
    (lanes[i][1] == 1 && lanes[(i + 2) % 4][3] == 1) ||
    (lanes[i][2] == 1 && lanes[(i + 1) % 4][3] == 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] as int >= 0 && s[i] as int <= 127
    requires ValidInputString(s)
    ensures result == "YES\n" || result == "NO\n"
    ensures exists input_lines :: 
        ParseInput(s, input_lines) && 
        (result == "YES\n" <==> AccidentPossible(input_lines))
    ensures |result| >= 3
// </vc-spec>
// <vc-code>
{
  var lanes: seq<seq<int>> := [];
  var pos := 0;
  var i := 0;
  while i < 4
    invariant 0 <= i <= 4
    invariant |lanes| == i
    invariant forall k :: 0 <= k < i ==> |lanes[k]| == 4
    invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < 4 ==> (lanes[k][j] == 0 || lanes[k][j] == 1)
    invariant pos <= |s|
    decreases 4 - i
  {
    var row: seq<int> := [];
    var j := 0;
    while j < 4
      invariant 0 <= j <= 4
      invariant |row| == j
      invariant forall k :: 0 <= k < j ==> (row[k] == 0 || row[k] == 1)
      invariant pos <= |s|
      decreases 4 - j
    {
      while pos < |s| && (s[pos] == ' ' || s[pos] == '\n')
        invariant pos <= |s|
        decreases |s| - pos
      {
        pos := pos + 1;
      }
      var v := 0;
      if pos < |s| && s[pos] == '1' {
        v := 1;
      } else {
        v := 0;
      }
      if pos < |s| {
        pos := pos + 1;
      }
      row := row + [v];
      j := j + 1;
    }
    lanes := lanes + [row];
    i := i + 1;
  }

  var accident := false;
  var li := 0;
  while li < 4
    invariant 0 <= li <= 4
    invariant accident ==> exists k :: 0 <= k < li && AccidentAtLane(k, lanes)
    invariant !accident ==> forall k :: 0 <= k < li ==> !AccidentAtLane(k, lanes)
    decreases 4 - li
  {
    var a0 := lanes[li][0];
    var a1 := lanes[li][1];
    var a2 := lanes[li][2];
    var a3 := lanes[li][3];
    var b0 := lanes[(li + 3) % 4][3];
    var b1 := lanes[(li + 2) % 4][3];
    var b2 := lanes[(li + 1) % 4][3];
    if (a3 == 1 && (a0 == 1 || a1 == 1 || a2 == 1)) ||
       (a0 == 1 && b0 == 1) ||
       (a1 == 1 && b1 == 1) ||
       (a2 == 1 && b2 == 1) {
      accident := true;
    }
    li := li + 1;
  }

  var inputLines := lanes;
  assert ParseInput(s, inputLines) by {
    assert |inputLines| == 4;
    assert forall k :: 0 <= k < 4 ==> |inputLines[k]| == 4;
    assert forall k :: 0 <= k < 4 ==> forall j :: 0 <= j < 4 ==> (inputLines[k][j] >= 0 && inputLines[k][j] <= 1);
    assert StringContainsFourLinesOfFourIntegers(s, inputLines);
  }

  if accident {
    assert AccidentPossible(inputLines);
    result := "YES\n";
  } else {
    assert !AccidentPossible(inputLines);
    result := "NO\n";
  }
}
// </vc-code>
