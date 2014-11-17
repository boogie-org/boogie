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


Running the tests
=================

Command line
------------

The ``run-unittests.py`` python script in the root directory of the project can be used to run the unit tests on the command line. This script is a simple wrapper for ``nunit-console.exe``.

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

Visual studio needs the "NUnit Test Adapter for VS2012 and VS2013" add-in to be installed (Tools > Extensions and Updates). Once that is installed you can run unit tests by going 

1. Going to the Test Explorer (TEST > Windows > Test Explorer)
2. Clicking on "Run All" in the Test Explorer.

