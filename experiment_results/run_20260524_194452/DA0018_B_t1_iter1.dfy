// <vc-preamble>
predicate ValidInput(m: int, d: int)
{
    1 <= m <= 12 && 1 <= d <= 7
}

function DaysInMonth(m: int): int
    requires 1 <= m <= 12
{
    [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][m-1]
}

function ColumnsNeeded(m: int, d: int): int
    requires ValidInput(m, d)
{
    1 + (d - 1 + DaysInMonth(m) - 1) / 7
}
// </vc-preamble>

// <vc-helpers>
lemma ColumnsNeededBounds(m: int, d: int)
    requires ValidInput(m, d)
    ensures 4 <= ColumnsNeeded(m, d) <= 6
{
    // DaysInMonth is between 28 and 31
    // d is between 1 and 7
    // (d - 1 + DaysInMonth(m) - 1) / 7 is between 3 and 5
    // so ColumnsNeeded is between 4 and 6
    var days := DaysInMonth(m);
    var offset := d - 1;
    // days in [28..31], offset in [0..6]
    // offset + days - 1 in [27..36]
    // (offset + days - 1) / 7 in [3..5]
    assert days == [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][m-1];
    assert 28 <= days <= 31;
    assert 0 <= offset <= 6;
    assert 27 <= offset + days - 1 <= 36;
    assert 3 <= (offset + days - 1) / 7 <= 5;
}
// </vc-helpers>

// <vc-spec>
method solve(m: int, d: int) returns (result: int)
    requires ValidInput(m, d)
    ensures result == ColumnsNeeded(m, d)
    ensures 4 <= result <= 6
// </vc-spec>
// <vc-code>
{
    ColumnsNeededBounds(m, d);
    var days := DaysInMonth(m);
    result := 1 + (d - 1 + days - 1) / 7;
}
// </vc-code>
