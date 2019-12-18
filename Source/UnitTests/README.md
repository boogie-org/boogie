Unit testing infrastructure
===========================

Boogie uses the [NUnit](http://www.nunit.org/) unit testing framework. 
We currently use NUnit 3.12.0.

Under .NET Core run the tests as follows:

```
$ dotnet test Source/Boogie-NetCore.sln
```

NUnit tests can also be run within most IDEs, like Visual Studio and
MonoDevelop.

## Legacy Build

**Installing NUnit**

* Library: `nuget restore Source/Boogie.sln`.
* Test runner: `nuget install -Version 3.10.0 NUnit.Console -OutputDirectory Source/packages/`

**Running the tests**

Make sure you have compiled the tests (the projects that end with ``Test``).

There is a wrapper script ``run-unitests.py`` around ``nunit3-console.exe`` to
run the unit tests. It takes the configuration to run as parameter.

```
$ python run-unittests.py Release
```

Run the following to see all the available options

```
$ python run-unittests.py --help
```
