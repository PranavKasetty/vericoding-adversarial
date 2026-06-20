// <vc-preamble>
predicate ValidInput(n: int, m: int, k: int, a: int, b: int) {
  n > 0 && m > 0 && k > 0 && 1 <= a <= n * m * k && 1 <= b <= n * m * k && a != b
}

function GetEntrance(apt: int, m: int, k: int): int
  requires apt >= 1
  requires m > 0 && k > 0
{
  (apt - 1) / (m * k)
}

function GetFloor(apt: int, m: int, k: int): int
  requires apt >= 1
  requires m > 0 && k > 0
{
  ((apt - 1) - GetEntrance(apt, m, k) * m * k) / k
}

function MinTravelTime(floors: int): int
  requires floors >= 0
{
  var stair_time := 5 * floors;
  var elevator_time := 10 + floors;
  if stair_time < elevator_time then stair_time else elevator_time
}

function MinEntranceDistance(entrance_a: int, entrance_b: int, n: int): int
  requires n > 0
{
  var clockwise := (entrance_b - entrance_a + n) % n;
  var counterclockwise := (entrance_a - entrance_b + n) % n;
  if clockwise <= counterclockwise then clockwise else counterclockwise
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): simplified lemmas to avoid nonlinear arithmetic timeout */
lemma GetEntranceNonNeg(apt: int, m: int, k: int)
  requires apt >= 1
  requires m > 0 && k > 0
  ensures GetEntrance(apt, m, k) >= 0
{
  assert m * k > 0;
  assert apt - 1 >= 0;
}

lemma GetFloorNonNeg(apt: int, m: int, k: int)
  requires apt >= 1
  requires m > 0 && k > 0
  ensures GetFloor(apt, m, k) >= 0
{
  var mk := m * k;
  assert mk > 0;
  var x := apt - 1;
  assert x >= 0;
  var q := x / mk;
  assert q >= 0;
  assert q * mk <= x;
  var r := x - q * mk;
  assert r >= 0;
  assert GetEntrance(apt, m, k) == q;
  assert GetFloor(apt, m, k) == r / k;
}

lemma MinTravelTimeNonNeg(floors: int)
  requires floors >= 0
  ensures MinTravelTime(floors) >= 0
{
}

lemma MinEntranceDistanceNonNeg(ea: int, eb: int, n: int)
  requires n > 0
  ensures MinEntranceDistance(ea, eb, n) >= 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int, a: int, b: int) returns (result: int)
  requires ValidInput(n, m, k, a, b)
  ensures result >= 0
  ensures GetEntrance(a, m, k) == GetEntrance(b, m, k) ==> 
    result == MinTravelTime(if GetFloor(a, m, k) >= GetFloor(b, m, k) 
                           then GetFloor(a, m, k) - GetFloor(b, m, k) 
                           else GetFloor(b, m, k) - GetFloor(a, m, k))
  ensures GetEntrance(a, m, k) != GetEntrance(b, m, k) ==>
    result == MinTravelTime(GetFloor(a, m, k)) + 
              15 * MinEntranceDistance(GetEntrance(a, m, k), GetEntrance(b, m, k), n) + 
              MinTravelTime(GetFloor(b, m, k))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): use intermediate variables and lemmas to help verifier */
  var mk := m * k;
  assert mk > 0;
  var entrance_a := GetEntrance(a, m, k);
  var entrance_b := GetEntrance(b, m, k);
  var floor_a := GetFloor(a, m, k);
  var floor_b := GetFloor(b, m, k);

  GetEntranceNonNeg(a, m, k);
  GetEntranceNonNeg(b, m, k);
  GetFloorNonNeg(a, m, k);
  GetFloorNonNeg(b, m, k);

  assert entrance_a >= 0;
  assert entrance_b >= 0;
  assert floor_a >= 0;
  assert floor_b >= 0;

  if entrance_a == entrance_b {
    var floor_diff := if floor_a >= floor_b then floor_a - floor_b else floor_b - floor_a;
    assert floor_diff >= 0;
    MinTravelTimeNonNeg(floor_diff);
    result := MinTravelTime(floor_diff);
    assert result >= 0;
    assert GetEntrance(a, m, k) == GetEntrance(b, m, k);
    assert floor_a == GetFloor(a, m, k);
    assert floor_b == GetFloor(b, m, k);
    assert floor_diff == (if GetFloor(a, m, k) >= GetFloor(b, m, k) then GetFloor(a, m, k) - GetFloor(b, m, k) else GetFloor(b, m, k) - GetFloor(a, m, k));
  } else {
    MinTravelTimeNonNeg(floor_a);
    MinTravelTimeNonNeg(floor_b);
    var entrance_dist := MinEntranceDistance(entrance_a, entrance_b, n);
    MinEntranceDistanceNonNeg(entrance_a, entrance_b, n);
    assert entrance_dist >= 0;
    result := MinTravelTime(floor_a) + 15 * entrance_dist + MinTravelTime(floor_b);
    assert result >= 0;
    assert GetEntrance(a, m, k) != GetEntrance(b, m, k);
    assert entrance_dist == MinEntranceDistance(GetEntrance(a, m, k), GetEntrance(b, m, k), n);
  }
}
// </vc-code>
