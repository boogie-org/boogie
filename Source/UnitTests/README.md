Unit testing infrastructure
===========================

Boogie uses the [NUnit](http://www.nunit.org/) unit testing framework. 
We currently use NUnit 3.12.0.

Installing NUnit
================

* Library: `nuget restore Source/Boogie.sln`.
* Test runner: `nuget install -Version 3.10.0 NUnit.Console -OutputDirectory Source/packages/`

Running the tests
=================

Command line
------------

Make sure you have compiled the tests (the projects that end with ``Test``).

You will then able to run the ``run-unitests.py`` script which is a convenient
wrapper around ``nunit3-console.exe`` to run the unittests. Here's an example
invocation. The parameter indicates the build type you are using.

```
$ python run-unittests.py Release
```

Run the following to see all the available options

```
$ python run-unittests.py --help
```

GUI
---

NUnit tests can be run within IDEs like Visual Studio and MonoDevelop
(potentially requiring the installation of a plugin).
