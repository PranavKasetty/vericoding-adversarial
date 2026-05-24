// <vc-preamble>
function string_to_digits(s: string): set<int>
{
    set i | 0 <= i < |s| && '0' <= s[i] <= '9' :: (s[i] as int) - ('0' as int)
}

predicate ValidInput(input: string)
{
    |input| > 0 && '\n' in input
}

predicate HasUniqueMovementSequence(digits: set<int>)
{
    (1 in digits || 4 in digits || 7 in digits || 0 in digits) &&
    (1 in digits || 2 in digits || 3 in digits) &&
    (3 in digits || 6 in digits || 9 in digits || 0 in digits) &&
    (7 in digits || 0 in digits || 9 in digits)
}

function split_lines(s: string): seq<string>
{
    if '\n' !in s then [s]
    else 
        var idx := find_char(s, '\n');
        if idx == -1 then [s]
        else if idx < |s| then [s[..idx]] + split_lines(s[idx+1..])
        else [s]
}
// </vc-preamble>

// <vc-helpers>
function find_char(s: string, c: char): int
{
    if |s| == 0 then -1
    else if s[0] == c then 0
    else 
        var rest := find_char(s[1..], c);
        if rest == -1 then -1 else rest + 1
}

lemma split_lines_nonempty(s: string)
    requires '
' in s
    ensures |split_lines(s)| >= 2
{
    var idx := find_char(s, '
');
    if idx == -1 {
    } else if idx < |s| {
    }
}

lemma find_char_in_string(s: string, c: char)
    requires c in s
    ensures find_char(s, c) >= 0
    ensures find_char(s, c) < |s|
    ensures s[find_char(s, c)] == c
{
    if s[0] == c {
    } else {
        find_char_in_string(s[1..], c);
    }
}

lemma find_char_not_neg_one(s: string, c: char)
    requires c in s
    ensures find_char(s, c) != -1
{
    find_char_in_string(s, c);
}

lemma split_lines_has_two(s: string)
    requires '
' in s
    ensures |split_lines(s)| >= 2
{
    find_char_not_neg_one(s, '
');
    var idx := find_char(s, '
');
    assert idx != -1;
    find_char_in_string(s, '
');
    assert idx < |s|;
}

lemma split_lines_second_element(s: string)
    requires '
' in s
    ensures |split_lines(s)| >= 2
    ensures 
        var idx := find_char(s, '
');
        idx != -1 && idx < |s| ==> split_lines(s)[1..] == split_lines(s[idx+1..])
{
    find_char_not_neg_one(s, '
');
    find_char_in_string(s, '
');
    var idx := find_char(s, '
');
    assert idx != -1;
    assert idx < |s|;
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
  requires ValidInput(input)
  ensures result == "YES\n" || result == "NO\n"
  ensures |result| > 0
  ensures var lines := split_lines(input);
          |lines| >= 2 ==>
          var digits_str := lines[1];
          var digits := string_to_digits(digits_str);
          result == "YES\n" <==> HasUniqueMovementSequence(digits)
// </vc-spec>
// <vc-code>
{
    var lines := split_lines(input);
    split_lines_has_two(input);
    var digits_str := lines[1];
    var digits := string_to_digits(digits_str);
    var has_unique := 
        (1 in digits || 4 in digits || 7 in digits || 0 in digits) &&
        (1 in digits || 2 in digits || 3 in digits) &&
        (3 in digits || 6 in digits || 9 in digits || 0 in digits) &&
        (7 in digits || 0 in digits || 9 in digits);
    if has_unique {
        result := "YES\n";
    } else {
        result := "NO\n";
    }
}
// </vc-code>
