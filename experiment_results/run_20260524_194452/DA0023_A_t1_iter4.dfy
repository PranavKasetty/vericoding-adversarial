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
/* helper modified by LLM (iteration 4): lemmas to help verifier with floor/entrance non-negativity */
lemma FloorNonNeg(apt: int, m: int, k: int)
  requires apt >= 1
  requires m > 0 && k > 0
  ensures GetFloor(apt, m, k) >= 0
{
  var mk := m * k;
  var ent := (apt - 1) / mk;
  assert ent >= 0;
  assert ent * mk <= apt - 1;
  var rem := (apt - 1) - ent * mk;
  assert rem >= 0;
  assert GetFloor(apt, m, k) == rem / k;
  assert rem / k >= 0;
}

lemma MinTravelTimeNonNeg(floors: int)
  requires floors >= 0
  ensures MinTravelTime(floors) >= 0
{
}

lemma EntranceDistNonNeg(ea: int, eb: int, n: int)
  requires n > 0
  ensures MinEntranceDistance(ea, eb, n) >= 0
{
  var cw := (eb - ea + n) % n;
  var ccw := (ea - eb + n) % n;
  assert cw >= 0;
  assert ccw >= 0;
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
  /* code modified by LLM (iteration 4): use lemmas to help verifier */
  var entrance_a := GetEntrance(a, m, k);
  var entrance_b := GetEntrance(b, m, k);
  var floor_a := GetFloor(a, m, k);
  var floor_b := GetFloor(b, m, k);

  FloorNonNeg(a, m, k);
  FloorNonNeg(b, m, k);
  assert floor_a >= 0;
  assert floor_b >= 0;

  if entrance_a == entrance_b {
    var floor_diff := if floor_a >= floor_b then floor_a - floor_b else floor_b - floor_a;
    assert floor_diff >= 0;
    MinTravelTimeNonNeg(floor_diff);
    result := MinTravelTime(floor_diff);
    assert result >= 0;
  } else {
    var entrance_dist := MinEntranceDistance(entrance_a, entrance_b, n);
    EntranceDistNonNeg(entrance_a, entrance_b, n);
    assert entrance_dist >= 0;
    MinTravelTimeNonNeg(floor_a);
    MinTravelTimeNonNeg(floor_b);
    assert MinTravelTime(floor_a) >= 0;
    assert MinTravelTime(floor_b) >= 0;
    result := MinTravelTime(floor_a) + 15 * entrance_dist + MinTravelTime(floor_b);
    assert result >= 0;
  }
}
// </vc-code>
