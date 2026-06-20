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
    if idx != -1 && idx < |s| {
        // split_lines returns [s[..idx]] + split_lines(s[idx+1..])
        // which has length >= 1 + 1 = 2 since split_lines always returns at least one element
    }
}

lemma find_char_in(s: string, c: char)
    requires c in s
    ensures find_char(s, c) != -1
    ensures 0 <= find_char(s, c) < |s|
    ensures s[find_char(s, c)] == c
{
    if s[0] == c {
    } else {
        assert c in s[1..];
        find_char_in(s[1..], c);
    }
}

lemma split_lines_with_newline(s: string)
    requires '
' in s
    ensures |split_lines(s)| >= 2
    ensures var idx := find_char(s, '
');
            idx != -1 && idx < |s| ==> split_lines(s) == [s[..idx]] + split_lines(s[idx+1..])
{
    find_char_in(s, '
');
    var idx := find_char(s, '
');
    assert idx != -1;
    assert s[idx] == '
';
    assert idx < |s|;
}

lemma split_lines_second_element(s: string)
    requires '
' in s
    ensures |split_lines(s)| >= 2
    ensures var idx := find_char(s, '
');
            split_lines(s)[1] == split_lines(s[idx+1..])[0]
{
    find_char_in(s, '
');
    var idx := find_char(s, '
');
    split_lines_with_newline(s);
}

lemma split_lines_first_is_prefix(s: string)
    requires '
' in s
    ensures split_lines(s)[0] == s[..find_char(s, '
')]
{
    find_char_in(s, '
');
    var idx := find_char(s, '
');
    split_lines_with_newline(s);
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
    var newline_pos := find_char(input, '
');
    find_char_in(input, '
');
    assert newline_pos != -1;
    assert newline_pos < |input|;
    assert input[newline_pos] == '
';
    
    var line1 := input[newline_pos+1..];
    
    // Show that split_lines(input)[1] == split_lines(line1)[0]
    split_lines_second_element(input);
    
    var digits := string_to_digits(line1);
    
    var has_unique := 
        (1 in digits || 4 in digits || 7 in digits || 0 in digits) &&
        (1 in digits || 2 in digits || 3 in digits) &&
        (3 in digits || 6 in digits || 9 in digits || 0 in digits) &&
        (7 in digits || 0 in digits || 9 in digits);
    
    // Verify that split_lines(input)[1] is line1
    var lines := split_lines(input);
    split_lines_with_newline(input);
    assert lines == [input[..newline_pos]] + split_lines(input[newline_pos+1..]);
    assert |lines| >= 2;
    assert lines[1] == split_lines(input[newline_pos+1..])[0];
    
    // split_lines of line1: if no newline, it's just [line1]
    var digits_str := lines[1];
    
    // We need: string_to_digits(digits_str) == digits
    // digits_str == split_lines(line1)[0]
    // If line1 has no newline, split_lines(line1) == [line1], so digits_str == line1
    // If line1 has a newline, digits_str == line1[..find_char(line1, '\n')]
    // In either case, string_to_digits could differ, but let's check
    
    // For the ensures, we need result == "YES\n" <==> HasUniqueMovementSequence(string_to_digits(digits_str))
    // digits_str is lines[1] = split_lines(line1)[0]
    // We computed digits = string_to_digits(line1)
    // These might differ if line1 contains '\n'
    
    // Let's recompute using digits_str directly
    var digits2 := string_to_digits(digits_str);
    
    var has_unique2 := 
        (1 in digits2 || 4 in digits2 || 7 in digits2 || 0 in digits2) &&
        (1 in digits2 || 2 in digits2 || 3 in digits2) &&
        (3 in digits2 || 6 in digits2 || 9 in digits2 || 0 in digits2) &&
        (7 in digits2 || 0 in digits2 || 9 in digits2);
    
    if has_unique2 {
        result := "YES\n";
    } else {
        result := "NO\n";
    }
}
// </vc-code>
