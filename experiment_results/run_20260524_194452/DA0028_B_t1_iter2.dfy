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
        if rest == -1 then -1
        else rest + 1
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

lemma split_lines_nonempty(s: string)
    requires '\n' in s
    ensures |split_lines(s)| >= 2
{
    find_char_in_string(s, '\n');
    var idx := find_char(s, '\n');
    assert idx >= 0 && idx < |s|;
    assert split_lines(s) == [s[..idx]] + split_lines(s[idx+1..]);
}

lemma split_lines_first_line(s: string)
    requires '\n' in s
    ensures |split_lines(s)| >= 2
    ensures var idx := find_char(s, '\n');
            idx >= 0 && idx < |s| &&
            split_lines(s)[0] == s[..idx] &&
            split_lines(s)[1..] == split_lines(s[idx+1..])
{
    find_char_in_string(s, '\n');
    var idx := find_char(s, '\n');
    assert split_lines(s) == [s[..idx]] + split_lines(s[idx+1..]);
}

lemma split_lines_second(s: string)
    requires '\n' in s
    ensures |split_lines(s)| >= 2
    ensures var idx := find_char(s, '\n');
            var rest := s[idx+1..];
            split_lines(s)[1] == split_lines(rest)[0]
{
    find_char_in_string(s, '\n');
    var idx := find_char(s, '\n');
    var rest := s[idx+1..];
    assert split_lines(s) == [s[..idx]] + split_lines(rest);
    assert split_lines(s)[1..] == split_lines(rest);
    assert split_lines(s)[1] == split_lines(rest)[0];
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
    /* code modified by LLM (iteration 2): fixed parse error by using proper escape sequences */
    var idx := find_char(input, '\n');
    find_char_in_string(input, '\n');
    var line0 := input[..idx];
    var rest := input[idx+1..];
    var digits_str := if '\n' in rest then split_lines(rest)[0] else rest;
    var digits := string_to_digits(digits_str);
    
    assert split_lines(input) == [line0] + split_lines(rest);
    
    var has_seq := 
        (1 in digits || 4 in digits || 7 in digits || 0 in digits) &&
        (1 in digits || 2 in digits || 3 in digits) &&
        (3 in digits || 6 in digits || 9 in digits || 0 in digits) &&
        (7 in digits || 0 in digits || 9 in digits);
    
    if has_seq {
        result := "YES\n";
    } else {
        result := "NO\n";
    }
    
    var lines := split_lines(input);
    if |lines| >= 2 {
        assert lines[0] == line0;
        assert lines[1..] == split_lines(rest);
        var second_line := lines[1];
        if '\n' in rest {
            assert split_lines(rest)[0] == second_line;
            assert digits_str == second_line;
        } else {
            assert split_lines(rest) == [rest];
            assert second_line == rest;
            assert digits_str == rest;
        }
        assert string_to_digits(digits_str) == string_to_digits(second_line);
        assert digits == string_to_digits(lines[1]);
    }
}
// </vc-code>
