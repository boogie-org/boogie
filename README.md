# Boogie

## Build Status

| Linux                         | Windows                         |
|-------------------------------|---------------------------------|
| [![linux build status][1]][2] | [![windows_build_status][3]][4] |

[1]: https://travis-ci.org/boogie-org/boogie.svg?branch=master
[2]: https://travis-ci.org/boogie-org/boogie
[3]: https://pmbuilds.inf.ethz.ch/buildStatus/icon?job=boogie
[4]: #FIXME

## About

Boogie is an intermediate verification language (IVL), intended as a layer on which
to build program verifiers for other languages. Several program verifiers have
been built in this way, including the VCC and HAVOC verifiers for C and the
verifiers for Dafny, Chalice, and Spec#. A previous version of the language was
called BoogiePL. The current language (version 2) is currently known as just
Boogie, which is also the name of the verification tool that takes Boogie
programs as input.

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

## Building

### Requirements

- [NuGet](https://www.nuget.org/)
- [Z3](https://github.com/Z3Prover/z3) 4.8.4 (earlier versions may also work, but the test suite assumes 4.8.4 to produce the expected output) or [CVC4](http://cvc4.cs.nyu.edu/web/) **FIXME_VERSION** (note
  CVC4 support is experimental)

#### Windows specific

- Visual Studio >= 2012

#### Linux/OSX specific

- Mono

### Windows

1. Open ``Source\Boogie.sln`` in Visual Studio
2. Right click the ``Boogie`` solution in the Solution Explorer and click ``Enable NuGet Package Restore``.
   You will probably get a prompt asking to confirm this. Choose ``Yes``.
3. Click ``BUILD > Build Solution``.

### Linux/OSX

You first need to fetch the NuGet packages that Boogie depends on. If you're doing this on the command line run

```
$ cd /path/to/repository
$ wget https://nuget.org/nuget.exe
$ mono ./nuget.exe restore Source/Boogie.sln
```

Note if you're using MonoDevelop it has a NuGet plug-in which you can use to "restore" the packages needed by Boogie.

Note if you see an error message like the following

```
WARNING: Error: SendFailure (Error writing headers)
Unable to find version '2.6.3' of package 'NUnit.Runners'.
```

then you need to initialise Mono's certificate store by running

```
$ mozroots --import --sync
```

then you can build by running

```
$ xbuild Source/Boogie.sln
```

Finally make sure there is a symlink to Z3 in the Binaries directory
(replace with ``cvc4`` if using CVC4 instead).

```
$ ln -s /usr/bin/z3 Binaries/z3.exe
```

## Running

On a Windows system call the Boogie binary:

```
$ Binaries\Boogie.exe
```

On a non-Windows system use the wrapper script:

```
$ Binaries/boogie
```

## Testing

Boogie has two forms of tests. Driver tests and unit tests

### Driver tests

See the [Driver test documentation](Test/README.md)

### Unit tests

See the [Unit test documentation](Source/UnitTests/README.md)
