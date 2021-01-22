# Boogie

[![License][license-badge]](LICENSE.txt)
[![NuGet package][nuget-badge]][nuget]

Boogie is an intermediate verification language (IVL), intended as a layer on
which to build program verifiers for other languages. Several program verifiers
have been built in this way, including the
[VCC](https://github.com/microsoft/vcc) and
[HAVOC](https://www.microsoft.com/en-us/research/project/havoc) verifiers for C
and the verifiers for [Dafny](https://github.com/dafny-lang/dafny),
[Chalice](https://www.microsoft.com/en-us/research/project/chalice), and
[Spec#](https://www.microsoft.com/en-us/research/project/spec).
For a sample verifier for a toy language built on top of Boogie, see
[Forro](https://github.com/boogie-org/forro).

Boogie is also the name of a tool. The tool accepts the Boogie language as
input, optionally infers some invariants in the given Boogie program, and then
generates verification conditions that are passed to an SMT solver. The default
SMT solver is [Z3](https://github.com/Z3Prover/z3).

## Documentation

Here are some resources to learn more about Boogie. Be aware that some
information might be incomplete or outdated.

* [Documentation](https://boogie-docs.readthedocs.org/en/latest/)
* [Language reference](https://boogie-docs.readthedocs.org/en/latest/LangRef.html).
* [This is Boogie 2](https://research.microsoft.com/en-us/um/people/leino/papers/krml178.pdf)
  details many aspects of the Boogie IVL but is slightly out of date.

## Getting help and contribute

You can ask questions and report issues on our [issue tracker](https://github.com/boogie-org/boogie/issues).

We are happy to receive contributions via [pull requests](https://github.com/boogie-org/boogie/pulls).

## Dependencies

Boogie requires [.NET Core](https://dotnet.microsoft.com) and a supported SMT
solver (see [below](#backend-smt-solver)).

## Installation

Boogie releases are packaged as a .NET Core global tool available at
[nuget.org][nuget]. To install Boogie simply run:

```
$ dotnet tool install --global boogie
```

## Building

To build Boogie run:

```
$ dotnet build Source/Boogie.sln
```

The compiled Boogie binary is
`Source/BoogieDriver/bin/${CONFIGURATION}/${FRAMEWORK}/BoogieDriver`.

## Backend SMT Solver

The default SMT solver for Boogie is [Z3](https://github.com/Z3Prover/z3).
Support for [CVC4](https://cvc4.github.io/) and
[Yices2](https://yices.csl.sri.com/) is experimental.

By default, Boogie looks for an executable called `z3|cvc4|yices2[.exe]` in your
`PATH` environment variable. If the solver executable is called differently on
your system, use `/proverOpt:PROVER_NAME=<exeName>`. Alternatively, an explicit
path can be given using `/proverOpt:PROVER_PATH=<path>`.

To learn how custom options can be supplied to the SMT solver (and more), call
Boogie with `/proverHelp`.

### Z3

The current test suite assumes version 4.8.8, but earlier and newer versions may
also work.

### CVC4 (experimental)

Call Boogie with `/proverOpt:SOLVER=CVC4`.

### Yices2 (experimental)

Call Boogie with `/proverOpt:SOLVER=Yices2 /useArrayTheory`.

Works for unquantified fragments, e.g. arrays + arithmetic + bitvectors. Does
not work for quantifiers, generalized arrays, datatypes.

## Testing

Boogie has two forms of tests. Driver tests and unit tests

### Driver tests

See the [Driver test documentation](Test/README.md)

### Unit tests

See the [Unit test documentation](Source/UnitTests/README.md)

## Versioning and Release

The current version of Boogie is noted in a [build property](Source/Directory.Build.props).
To push a new version to nuget, perform the following steps:

- Update the version (e.g., x.y.z) and commit the change
- git tag vx.y.z
- git push vx.y.z

The [CI workflow](.github/workflows/test.yml) will build and push the packages.

## License

Boogie is licensed under the MIT License (see [LICENSE.txt](LICENSE.txt)).

[license-badge]: https://img.shields.io/github/license/boogie-org/boogie?color=blue
[nuget]:         https://www.nuget.org/packages/Boogie
[nuget-badge]:   https://img.shields.io/nuget/v/Boogie
