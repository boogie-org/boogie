// RUN: %parallel-boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:builtin "str.++"} concat(string, string): string;
function {:builtin "str.len"} len(string): int;
function {:builtin "str.substr"} substr(string, int, int): string;
function {:builtin "str.indexof"} indexOf(string, string): int;
function {:builtin "str.indexof"} indexOfFromOffset(string, string, int): int;
function {:builtin "str.at"} at(string, int): string;
function {:builtin "str.contains"} contains(string, string): bool;
function {:builtin "str.prefixof"} prefixOf(string, string): bool;
function {:builtin "str.suffixof"} suffixOf(string, string): bool;
function {:builtin "str.replace"} replace(string, string, string): string;
function {:builtin "str.to.int"} stringToInt(string): int;
function {:builtin "int.to.str"} intToString(int): string;

procedure main() {
    assert concat("abc", "def") == "abcdef";

    assert len("abcd") == 4;

    assert substr("abcd", 1, 2) == "bc";

    assert indexOf("abcd", "cd") == 2;
    assert indexOf("abcd", "dc") == -1;

    assert indexOfFromOffset("abcdabcd", "cd", 0) == 2;
    assert indexOfFromOffset("abcdabcd", "cd", 3) == 6;
    assert indexOfFromOffset("abcdabcd", "dc", 1) == -1;

    assert at("abcd", 2) == "c";

    assert contains("abcd", "bc");
    assert !contains("abcd", "BC");

    assert prefixOf("ab", "abcd");
    assert !prefixOf("AB", "abcd");

    assert suffixOf("cd", "abcd");
    assert !suffixOf("CD", "abcd");

    assert replace("aBCd", "BC", "bc") == "abcd";

    assert stringToInt("42") == 42;

    assert intToString(42) == "42";
}
