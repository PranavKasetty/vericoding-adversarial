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
lemma DeviationLemma(cameraAngle: int, r: int)
    requires 0 <= r <= 3
    ensures 0 <= ImageAngleAfterRotations(cameraAngle, r) < 360
{
    var n := (-cameraAngle + 90 * r) % 360;
    if n < 0 {
    } else {
    }
}

lemma NormalizeAngleRange(angle: int)
    ensures 0 <= NormalizeAngle(angle) < 360
{
    var n := angle % 360;
    if n < 0 {
        assert n + 360 >= 0;
        assert n + 360 < 360;
    } else {
        assert n >= 0;
        assert n < 360;
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
    var best := 0;
    var i := 1;
    while i <= 3
        invariant 1 <= i <= 4
        invariant 0 <= best <= 3
        invariant best < i
        invariant forall k :: 0 <= k < i ==> 
            var bd := ImageDeviationAfterRotations(x, best);
            var kd := ImageDeviationAfterRotations(x, k);
            bd < kd || (bd == kd && best <= k)
    {
        NormalizeAngleRange(-x + 90 * best);
        NormalizeAngleRange(-x + 90 * i);
        var best_dev := ImageDeviationAfterRotations(x, best);
        var i_dev := ImageDeviationAfterRotations(x, i);
        if i_dev < best_dev {
            best := i;
        }
        i := i + 1;
    }
    result := best;
}
// </vc-code>
