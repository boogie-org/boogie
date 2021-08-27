// RUN: %parallel-boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "str.to.re"} stringToRegEx(string): regex;
function {:builtin "str.in.re"} stringInRegEx(string, regex): bool;
function {:builtin "re.allchar"} allChar(): regex;
function {:builtin "re.nostr"} noString(): regex;
function {:builtin "re.range"} range(string, string): regex;
function {:builtin "re.++"} concat(regex, regex): regex;
function {:builtin "re.*"} star(regex): regex;
function {:builtin "re.+"} plus(regex): regex;
function {:builtin "re.opt"} option(regex): regex;
function {:builtin "re.loop"} loop(regex, int, int): regex;
function {:builtin "re.union"} union(regex, regex): regex;
function {:builtin "re.inter"} intersection(regex, regex): regex;

procedure main() {
    var s1: string;
    var r1: regex;

    s1 := "abcd";
    r1 := stringToRegEx(s1);

    assert stringInRegEx(s1, stringToRegEx(s1));
    assert !stringInRegEx(s1, stringToRegEx("ABCD"));

    assert stringInRegEx(s1, star(allChar()));

    assert !stringInRegEx(s1, noString());

    assert !stringInRegEx(s1, concat(noString(), noString()));

    assert stringInRegEx(s1, option(plus(allChar())));

    assert !stringInRegEx(s1, loop(noString(), 0, 5));
    assert stringInRegEx(s1, loop(allChar(), 0, 5));

    assert !stringInRegEx(s1, union(noString(), noString()));
    assert stringInRegEx(s1, intersection(star(allChar()), star(allChar())));

}

