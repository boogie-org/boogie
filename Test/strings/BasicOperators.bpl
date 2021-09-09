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
    var s1, s2, s3: string;

    assume len(s1) == 3;
    assume len(s3) == 3;
    assume concat(s1,s2) == s3;

    assert len(s1) + len(s2) == len(s3);

    assert substr(s3, len(s1), len(s2)) == s2;

    assert indexOf(s3, s1) == 0;

    assert indexOfFromOffset(s3, s1, 0) == 0;

    assert at(s3, 2) == at(s1, 2);

    assert contains(s3, s1);

    assert prefixOf(s1, s3);

    assert suffixOf(s2, s3);

    assert replace(s3, s1, s2) == concat(s2, s2);

    // TODO: This used to verify with Z3 4.8.4
    // assert intToString(stringToInt(s1)) == s1;
}
