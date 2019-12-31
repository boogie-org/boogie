# Boogie

## Build Status

| Linux                         | Windows                         |
|-------------------------------|---------------------------------|
| [![linux build status][1]][2] | [![windows_build_status][3]][4] |

[1]: https://travis-ci.com/boogie-org/boogie.svg?branch=master
[2]: https://travis-ci.com/boogie-org/boogie
[3]: https://pmbuilds.inf.ethz.ch/buildStatus/icon?job=boogie
[4]: #FIXME

## About

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
A previous version of the language was called BoogiePL. The current language
(version 2) is currently known as just Boogie, which is also the name of the
verification tool that takes Boogie programs as input.

Boogie is also the name of a tool. The tool accepts the Boogie language as
input, optionally infers some invariants in the given Boogie program, and then
generates verification conditions that are passed to an SMT solver. The default
SMT solver is [Z3](https://github.com/Z3Prover/z3).

The Boogie research project is being developed primarily in the [RiSE
group](http://research.microsoft.com/rise) at [Microsoft
Research](http://research.microsoft.com/) in Redmond. However, people at
several other institutions make the open-source Boogie tool what it is.

![boogie architecture](http://research.microsoft.com/en-us/projects/boogie/boogie.png)

More documentation can be found at http://boogie-docs.readthedocs.org/en/latest/ .

## Language Reference

See [Language reference](http://boogie-docs.readthedocs.org/en/latest/LangRef.html).

Note: [This is Boogie2](http://research.microsoft.com/en-us/um/people/leino/papers/krml178.pdf) details
many aspects of the Boogie IVL but is slightly out of date.

## Getting help

We have a public [mailing list](https://mailman.ic.ac.uk/mailman/listinfo/boogie-dev) for users of Boogie.
You can also report issues on our [issue tracker](https://github.com/boogie-org/boogie/issues)

## Installation

Boogie releases are packaged as a .NET Core global tool available at
[nuget.org](https://www.nuget.org/packages/Boogie). To install Boogie simply
run:

```
$ dotnet tool install --global boogie
```

To run Boogie, a supported SMT solver has to be available (see below).

## Building

The preferred way to build (and run) Boogie today is using .NET Core.
Historically, Boogie can also be built using the classic .NET Framework (on
Windows) and Mono (on Linux/OSX), but this might not be supported in the future.

To run Boogie, a supported SMT solver has to be available (see below).

### .NET Core

```
$ dotnet build Source/Boogie-NetCore.sln
```

The compiled Boogie binary is
`Source/BoogieDriver/bin/${CONFIGURATION}/${FRAMEWORK}/BoogieDriver`. Also, a
NuGet package is placed in `Source/BoogieDriver/bin/Debug/` which can be used
for a local installation.

### Windows (requires Visual Studio)

1. Open ``Source\Boogie.sln`` in Visual Studio.
2. Right click the ``Boogie`` solution in the Solution Explorer and click ``Restore NuGet Packages``.
3. Click ``Build > Build Solution``.

The compiled Boogie binary is `Binaries\Boogie.exe`.

### Linux/OSX (requires Mono)

Either open ``Source\Boogie.sln`` in MonoDevelop and perform the same steps as
described for Visual Studio above, of compile on the command line as follows.

Fetch the NuGet packages that Boogie depends on:

```
$ nuget restore Source/Boogie.sln
```

Build Boogie:

```
$ msbuild Source/Boogie.sln
```

The compiled Boogie binary is `Binaries/Boogie.exe`, which can be executed with
`mono` or using the wrapper script `Binaries/boogie`.

## Backend SMT Solver

The default SMT solver for Boogie is [Z3](https://github.com/Z3Prover/z3).
Support for [CVC4](https://cvc4.github.io/) and
[Yices2](https://yices.csl.sri.com/) is experimental.

### Z3

The current test suite assumes version 4.8.7, but earlier and newer versions may
also work.

Option 1: Make sure a Z3 executable called `z3` or `z3.exe` is in your `PATH`
environment variable.

Option 2: Call Boogie with `/z3exe:<path>`.

### CVC4 (experimental)

Call Boogie with `/proverOpt:SOLVER=CVC4 /cvc4exe:<path>`.

### Yices2 (experimental)

Call Boogie with `/proverOpt:SOLVER=Yices2 /yices2exe:<path> /useArrayTheory`.

Works for unquantified fragments, e.g. arrays + arithmetic + bitvectors. Does
not work for quantifiers, generalized arrays, datatypes.

## Testing

Boogie has two forms of tests. Driver tests and unit tests

### Driver tests

See the [Driver test documentation](Test/README.md)

### Unit tests

See the [Unit test documentation](Source/UnitTests/README.md)

## Versioning and Release Automation

The https://github.com/boogie-org/boogie/blob/master/.github/workflows/main.yml workflow will create and push a new tag each time commits are pushed to the master branch (including PR merges). By default, the created tag increments the patch version number from the previous tag. For example, if the last tagged commit were `v2.4.3`, then pushing to master would tag the latest commit with `v2.4.4`. If incrementing minor or major number is desired instead of patch, simply add `#minor` or `#major` to the first line of the commit message. For instance:
> Adding the next greatest feature. #minor

If the last tagged commit were `v2.4.3`, then pushing this commit would generate the tag `v2.5.0`.

For pull-request merges, if minor or major version increments are desired, the first line of the merge commit message can be changed to include `#minor` or `#major`.

Note that on each push to `master`, the following will happen:
* A travis build for `master` is triggered.
* The GitHub workflow is also triggered.
* Once the workflow pushes a new tag `vX.Y.Z`, another travis build for `vX.Y.Z` is triggered.
* The travis build for `vX.Y.Z` in Release configuration publishes releases to GitHub and [NuGet.org](https://www.nuget.org/packages/Boogie/).

## License

Boogie is licensed under the MIT License (see [LICENSE.txt](LICENSE.txt)).
