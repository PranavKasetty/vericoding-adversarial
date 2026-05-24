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
/* helper modified by LLM (iteration 4): lemmas to help verifier with floor/entrance bounds */
lemma GetFloorNonNeg(apt: int, m: int, k: int)
  requires apt >= 1
  requires m > 0 && k > 0
  ensures GetFloor(apt, m, k) >= 0
{
  var e := GetEntrance(apt, m, k);
  assert e == (apt - 1) / (m * k);
  assert e >= 0;
  assert e * m * k <= apt - 1;
  assert (apt - 1) - e * m * k >= 0;
}

lemma GetEntranceNonNeg(apt: int, m: int, k: int)
  requires apt >= 1
  requires m > 0 && k > 0
  ensures GetEntrance(apt, m, k) >= 0
{
  assert (apt - 1) >= 0;
  assert m * k > 0;
}

lemma MinEntranceDistNonNeg(entrance_a: int, entrance_b: int, n: int)
  requires n > 0
  ensures MinEntranceDistance(entrance_a, entrance_b, n) >= 0
{
  var clockwise := (entrance_b - entrance_a + n) % n;
  var counterclockwise := (entrance_a - entrance_b + n) % n;
  assert clockwise >= 0;
  assert counterclockwise >= 0;
}

lemma MinTravelTimeNonNeg(floors: int)
  requires floors >= 0
  ensures MinTravelTime(floors) >= 0
{
  assert 5 * floors >= 0;
  assert 10 + floors >= 0;
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
  /* code modified by LLM (iteration 4): use lemmas to guide verifier, avoid timeout */
  GetFloorNonNeg(a, m, k);
  GetFloorNonNeg(b, m, k);
  GetEntranceNonNeg(a, m, k);
  GetEntranceNonNeg(b, m, k);
  var entrance_a := GetEntrance(a, m, k);
  var entrance_b := GetEntrance(b, m, k);
  var floor_a := GetFloor(a, m, k);
  var floor_b := GetFloor(b, m, k);
  MinTravelTimeNonNeg(floor_a);
  MinTravelTimeNonNeg(floor_b);
  if entrance_a == entrance_b {
    var floor_diff := if floor_a >= floor_b then floor_a - floor_b else floor_b - floor_a;
    assert floor_diff >= 0;
    MinTravelTimeNonNeg(floor_diff);
    result := MinTravelTime(floor_diff);
  } else {
    MinEntranceDistNonNeg(entrance_a, entrance_b, n);
    var entrance_dist := MinEntranceDistance(entrance_a, entrance_b, n);
    assert entrance_dist >= 0;
    result := MinTravelTime(floor_a) + 15 * entrance_dist + MinTravelTime(floor_b);
  }
}
// </vc-code>
