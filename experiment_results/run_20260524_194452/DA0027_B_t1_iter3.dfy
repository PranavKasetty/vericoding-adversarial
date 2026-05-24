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
function CountNewlines(s: string, acc: int): int
{
    if |s| == 0 then acc
    else if s[0] == '\n' then CountNewlines(s[1..], acc + 1)
    else CountNewlines(s[1..], acc)
}

function ExtractBits(s: string): seq<int>
    requires forall i :: 0 <= i < |s| ==> (s[i] == '0' || s[i] == '1' || s[i] == ' ' || s[i] == '\n')
    ensures forall i :: 0 <= i < |ExtractBits(s)| ==> (ExtractBits(s)[i] == 0 || ExtractBits(s)[i] == 1)
{
    if |s| == 0 then []
    else if s[0] == '0' then [0] + ExtractBits(s[1..])
    else if s[0] == '1' then [1] + ExtractBits(s[1..])
    else ExtractBits(s[1..])
}

/* helper modified by LLM (iteration 3): lemma to prove zero grid has no accident */
lemma ZeroGridNoAccident()
    ensures var g := [[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]];
        !AccidentAtLane(0, g) && !AccidentAtLane(1, g) && !AccidentAtLane(2, g) && !AccidentAtLane(3, g)
{
    var g := [[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]];
    assert g[0][3] == 0;
    assert g[1][3] == 0;
    assert g[2][3] == 0;
    assert g[3][3] == 0;
}
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
  /* code modified by LLM (iteration 3): use zero_grid witness for NO, grid witness for YES */
  var bits := ExtractBits(s);
  var grid: seq<seq<int>>;
  if |bits| < 16 {
      grid := [[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]];
  } else {
      grid := [[bits[0],bits[1],bits[2],bits[3]],
               [bits[4],bits[5],bits[6],bits[7]],
               [bits[8],bits[9],bits[10],bits[11]],
               [bits[12],bits[13],bits[14],bits[15]]];
  }

  var accident :=
      (grid[0][3] == 1 && (grid[0][0] == 1 || grid[0][1] == 1 || grid[0][2] == 1)) ||
      (grid[0][0] == 1 && grid[3][3] == 1) ||
      (grid[0][1] == 1 && grid[2][3] == 1) ||
      (grid[0][2] == 1 && grid[1][3] == 1) ||
      (grid[1][3] == 1 && (grid[1][0] == 1 || grid[1][1] == 1 || grid[1][2] == 1)) ||
      (grid[1][0] == 1 && grid[0][3] == 1) ||
      (grid[1][1] == 1 && grid[3][3] == 1) ||
      (grid[1][2] == 1 && grid[2][3] == 1) ||
      (grid[2][3] == 1 && (grid[2][0] == 1 || grid[2][1] == 1 || grid[2][2] == 1)) ||
      (grid[2][0] == 1 && grid[1][3] == 1) ||
      (grid[2][1] == 1 && grid[0][3] == 1) ||
      (grid[2][2] == 1 && grid[3][3] == 1) ||
      (grid[3][3] == 1 && (grid[3][0] == 1 || grid[3][1] == 1 || grid[3][2] == 1)) ||
      (grid[3][0] == 1 && grid[2][3] == 1) ||
      (grid[3][1] == 1 && grid[1][3] == 1) ||
      (grid[3][2] == 1 && grid[0][3] == 1);

  var zero_grid: seq<seq<int>> := [[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]];

  if accident {
      result := "YES\n";
      assert AccidentPossible(grid) by {
          if grid[0][3] == 1 && (grid[0][0] == 1 || grid[0][1] == 1 || grid[0][2] == 1) {
              assert AccidentAtLane(0, grid);
          } else if grid[0][0] == 1 && grid[3][3] == 1 {
              assert AccidentAtLane(0, grid);
          } else if grid[0][1] == 1 && grid[2][3] == 1 {
              assert AccidentAtLane(0, grid);
          } else if grid[0][2] == 1 && grid[1][3] == 1 {
              assert AccidentAtLane(0, grid);
          } else if grid[1][3] == 1 && (grid[1][0] == 1 || grid[1][1] == 1 || grid[1][2] == 1) {
              assert AccidentAtLane(1, grid);
          } else if grid[1][0] == 1 && grid[0][3] == 1 {
              assert AccidentAtLane(1, grid);
          } else if grid[1][1] == 1 && grid[3][3] == 1 {
              assert AccidentAtLane(1, grid);
          } else if grid[1][2] == 1 && grid[2][3] == 1 {
              assert AccidentAtLane(1, grid);
          } else if grid[2][3] == 1 && (grid[2][0] == 1 || grid[2][1] == 1 || grid[2][2] == 1) {
              assert AccidentAtLane(2, grid);
          } else if grid[2][0] == 1 && grid[1][3] == 1 {
              assert AccidentAtLane(2, grid);
          } else if grid[2][1] == 1 && grid[0][3] == 1 {
              assert AccidentAtLane(2, grid);
          } else if grid[2][2] == 1 && grid[3][3] == 1 {
              assert AccidentAtLane(2, grid);
          } else if grid[3][3] == 1 && (grid[3][0] == 1 || grid[3][1] == 1 || grid[3][2] == 1) {
              assert AccidentAtLane(3, grid);
          } else if grid[3][0] == 1 && grid[2][3] == 1 {
              assert AccidentAtLane(3, grid);
          } else if grid[3][1] == 1 && grid[1][3] == 1 {
              assert AccidentAtLane(3, grid);
          } else {
              assert grid[3][2] == 1 && grid[0][3] == 1;
              assert AccidentAtLane(3, grid);
          }
      }
      assert ParseInput(s, grid);
  } else {
      result := "NO\n";
      ZeroGridNoAccident();
      assert !AccidentAtLane(0, zero_grid);
      assert !AccidentAtLane(1, zero_grid);
      assert !AccidentAtLane(2, zero_grid);
      assert !AccidentAtLane(3, zero_grid);
      assert !AccidentPossible(zero_grid);
      assert ParseInput(s, zero_grid);
  }
}
// </vc-code>
