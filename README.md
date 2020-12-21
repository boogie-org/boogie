# Boogie

[![License][license-badge]](LICENSE.txt)
[![NuGet package][nuget-badge]][nuget]
[![Travis build status][travis-badge]][travis]

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

## Versioning and Release Automation

The [Bump workflow](.github/workflows/main.yml) will create and push a new tag
each time commits are pushed to the master branch (including PR merges). By
default, the created tag increments the patch version number from the previous
tag. For example, if the last tagged commit were `v2.4.3`, then pushing to
master would tag the latest commit with `v2.4.4`. If incrementing minor or major
number is desired instead of patch, simply add `#minor` or `#major` anywhere in
the commit message. For instance:

> Adding the next greatest feature. #minor

If the last tagged commit were `v2.4.3`, then pushing this commit would generate
the tag `v2.5.0`.

For pull-request merges, if minor or major version increments are desired, the
first line of the merge commit message can be changed to include `#minor` or
`#major`.

Note that on each push to `master`, the following will happen:
* A travis build for `master` is triggered.
* The GitHub workflow is also triggered.
* Once the workflow pushes a new tag `vX.Y.Z`, another travis build for `vX.Y.Z`
  is triggered.
* The travis build for `vX.Y.Z` in Release configuration publishes releases to
  GitHub and [NuGet.org][nuget].

## License

Boogie is licensed under the MIT License (see [LICENSE.txt](LICENSE.txt)).

[license-badge]: https://img.shields.io/github/license/boogie-org/boogie?color=blue
[nuget]:         https://www.nuget.org/packages/Boogie
[nuget-badge]:   https://img.shields.io/nuget/v/Boogie
[travis]:        https://travis-ci.com/boogie-org/boogie
[travis-badge]:  https://travis-ci.com/boogie-org/boogie.svg?branch=master
[jenkins]:       #FIXME
[jenkins-badge]: https://pmbuilds.inf.ethz.ch/buildStatus/icon?job=boogie
