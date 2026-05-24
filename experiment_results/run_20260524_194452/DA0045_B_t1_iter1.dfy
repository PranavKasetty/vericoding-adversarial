// <vc-preamble>
function NormalizeAngle(angle: int): int
{
    var n := angle % 360;
    if n < 0 then n + 360 else n
}

function DeviationFromVertical(angle: int): int
    requires 0 <= angle < 360
{
    if angle <= 180 then angle else 360 - angle
}

function ImageAngleAfterRotations(cameraAngle: int, rotations: int): int
    requires 0 <= rotations <= 3
{
    NormalizeAngle(-cameraAngle + 90 * rotations)
}

function ImageDeviationAfterRotations(cameraAngle: int, rotations: int): int
    requires 0 <= rotations <= 3
{
    DeviationFromVertical(ImageAngleAfterRotations(cameraAngle, rotations))
}

predicate IsOptimalRotations(cameraAngle: int, result: int)
    requires 0 <= result <= 3
{
    forall k :: 0 <= k <= 3 ==> 
        var result_deviation := ImageDeviationAfterRotations(cameraAngle, result);
        var k_deviation := ImageDeviationAfterRotations(cameraAngle, k);
        result_deviation < k_deviation || (result_deviation == k_deviation && result <= k)
}
// </vc-preamble>

// <vc-helpers>
lemma DeviationBounds(angle: int)
    requires 0 <= angle < 360
    ensures 0 <= DeviationFromVertical(angle) <= 180
{
}

lemma NormalizeAngleRange(angle: int)
    ensures 0 <= NormalizeAngle(angle) < 360
{
    var n := angle % 360;
    if n < 0 {
    } else {
    }
}

lemma ImageAngleRange(cameraAngle: int, rotations: int)
    requires 0 <= rotations <= 3
    ensures 0 <= ImageAngleAfterRotations(cameraAngle, rotations) < 360
{
    NormalizeAngleRange(-cameraAngle + 90 * rotations);
}

lemma ComputeOptimal(x: int) returns (best: int)
    ensures 0 <= best <= 3
    ensures IsOptimalRotations(x, best)
{
    ImageAngleRange(x, 0);
    ImageAngleRange(x, 1);
    ImageAngleRange(x, 2);
    ImageAngleRange(x, 3);
    DeviationBounds(ImageAngleAfterRotations(x, 0));
    DeviationBounds(ImageAngleAfterRotations(x, 1));
    DeviationBounds(ImageAngleAfterRotations(x, 2));
    DeviationBounds(ImageAngleAfterRotations(x, 3));
    var d0 := ImageDeviationAfterRotations(x, 0);
    var d1 := ImageDeviationAfterRotations(x, 1);
    var d2 := ImageDeviationAfterRotations(x, 2);
    var d3 := ImageDeviationAfterRotations(x, 3);
    // Find best: smallest deviation, tie-break by smallest index
    var b := 0;
    var db := d0;
    if d1 < db {
        b := 1;
        db := d1;
    }
    if d2 < db {
        b := 2;
        db := d2;
    }
    if d3 < db {
        b := 3;
        db := d3;
    }
    best := b;
    // Now prove IsOptimalRotations
    assert forall k :: 0 <= k <= 3 ==> 
        ImageDeviationAfterRotations(x, best) < ImageDeviationAfterRotations(x, k) || 
        (ImageDeviationAfterRotations(x, best) == ImageDeviationAfterRotations(x, k) && best <= k) by {
        forall k | 0 <= k <= 3 {
            if k == 0 {
                assert db <= d0 && (db < d0 || best <= 0);
            } else if k == 1 {
                assert db <= d1 && (db < d1 || best <= 1);
            } else if k == 2 {
                assert db <= d2 && (db < d2 || best <= 2);
            } else {
                assert db <= d3 && (db < d3 || best <= 3);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
    ensures 0 <= result <= 3
    ensures IsOptimalRotations(x, result)
// </vc-spec>
// <vc-code>
{
    result := ComputeOptimal(x);
}
// </vc-code>
