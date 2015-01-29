Unit testing infrastructure
===========================

Boogie uses [NUnit](http://www.nunit.org/) unit test framework.
We currently use NUnit 2.6.3, which was the latest stable
version available at the time of writing.


Installing NUnit
================

NUnit should be installed via [NuGet](https://www.nuget.org/) package manager.

The NuGet client is available as

* An extension to Visual Studio
* An add-in in Monodevelop
* A command line utility from the NuGet website

Note Mono ships with an old version of NUnit (2.4.8) which will cause
compilation issues. To fix this you must install NUnit via NuGet.

Visual Studio
-------------

Visual Studio should automatically download the missing NuGet packages
when the solution is built. If this doesn't work make sure the
``Allow NuGet to download missing packages`` checkbox is ticked in
``TOOLS > NuGet Package Manager > Package Manager Settings``.

If for some reason this does not work right click the Boogie Solution in the
Solution Explorer and click ``Enable NuGet Package Restore``.

Monodevelop
-----------

To obtain NUnit Right click the Solution (Boogie) in the ``Solution Explorer``
and click ``Restore NuGet packages``. This will download any NuGet packages that
Boogie depends on (currently just NUnit).

Command line utility
--------------------

NuGet is available as a standalone command line utility. Here is an example set
of commands that will download the NUnit NuGet package when run from the root of
the Boogie repository.

```
$ wget https://nuget.org/nuget.exe
$ mono nuget.exe restore Source/Boogie.sln
```

Note if you see an error like this when running ``nuget.exe``

```
WARNING: Error: SendFailure (Error writing headers)
```

it will probably be because the trusted root certificates aren't setup for mono.
To set this up run the following.

```
$ mozroots --import --sync
```


Running the tests
=================

Command line
------------

Before you start you need to install the "NUnit.Runners" package to run
``nunit-console.exe``. To do this run

```
$ cd Source/packages/
$ mono ./nuget.exe install -Version 2.6.3 NUnit.Runners
```

Then make sure you have compiled the tests (the projects in the solution that
have the ``Test`` suffix).

You will then able to run the ``run-unitests.py`` script which is a convenient
wrapper around ``nunit-console.exe`` to run the unittests. Here's an example
invocation. The positional parameter indicates the build type you are using.

```
$ python run-unittests.py Release
```

Run the following to see all the available options

```
$ python run-unittests.py --help
```

Monodevelop
-----------

Monodevelop has built in support for running NUnit tests. Goto the "Unit Tests"
panel and click "Run All".

Visual Studio
-------------

Visual studio needs the "NUnit Test Adapter for VS2012 and VS2013" add-in to be
installed (Tools > Extensions and Updates).  Once that is installed you can run
unit tests by

1. Going to the Test Explorer (TEST > Windows > Test Explorer)
2. Clicking on "Run All" in the Test Explorer.

