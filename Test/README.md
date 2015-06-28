Testing infrastructure
----------------------

Boogie uses LLVM's [lit tool](http://llvm.org/docs/CommandGuide/lit.html) for
testing and the [OutputCheck tool](https://github.com/stp/OutputCheck). This
infrastructure should work on Linux, OSX and Windows.

Setting up the test environment
-------------------------------

First make sure you have Python installed. We use Python 3.4 but older versions
should work as well.

The lit and OutputCheck tools are both available in
[PyPi](https://pypi.python.org/pypi). Install the
[pip](http://pip.readthedocs.org/en/latest/installing.html) tool if you don't
already have have it and then run

```
$ pip install lit
$ pip install OutputCheck
```

this will install the tools on your system. If you are running on Linux/OSX and
do not have root access then you can use the
[virtualenv](http://virtualenv.readthedocs.org/en/latest/) tool to install these
tools without the need for root access.

Once installed check the tools are available on your PATH.

```
$ lit --help
Usage: lit [options] {file-or-path}

Options:
  -h, --help            show this help message and exit
...

$ OutputCheck --help
usage: OutputCheck [-h] [--file-to-check= FILE_TO_CHECK=]
                   [--check-prefix= CHECK_PREFIX=]
                   [-l {debug,info,warning,error}] [--comment= COMMENT=] [-d]
                   [--disable-substitutions]
                   check_file
...
```

On Windows it may be necessary to add the Python scripts folder
(e.g. ``C:\Python34\Scripts\``) to your PATH if the above commands do not work.

Other requirements
------------------

We currently require Z3 4.<FIXME> to be used with the test suite.


Running the tests
-----------------

lit is a very flexible tool. You simply pass it one or more paths to directories
or individual tests (usually .bpl files) and lit will build up a list of tests
to run.

For example to run the whole test suite run the following command

```
$ cd Test
$ lit .
```

For example to run all tests in the ``test1`` folder and the bla1.bpl and
constants.bpl test run the following command

```
$ cd Test
$ lit test0/ livevars/bla1.bpl aitest0/constants.bpl
```

Note replace ``/`` with ``\`` on Windows (tab completition is your friend).

If you would prefer to see less information when running tests you can use the
``-s`` flag to show progress information and a summary when tests finish.

```
$ cd Test
$ lit -s .
```

To pass additional flags to Boogie when running tests run the following command
where ``-someParamter`` is a paramter Boogie supports.

```
$ cd Test
$ lit --param boogie_params='-someParameter' .
```

For more ``lit`` options run

```
$ lit --help
```

Debugging failing tests
-----------------------

You can pass the ``-v`` flag to get more verbose output to try to determine why
certains tests are failing.

```
$ cd Test
$ lit -v livevars/bla1.bpl
```

Removing output produced by tests
---------------------------------

lit will by default create a folder named ``Output`` in each directory that
will contain temporary files created by tests.  You can run the following to
remove all these folders/files.

```
$ cd Test
$ ./clean.py
```

This script will also remove old files created by the legacy batch file based
testing infrastructure (no longer in source tree). If temporary files are left
behind from the old testing infrastructure it is necessary to run this script
to remove those files before using ``lit``.

Writing tests
-------------

Tests are driven my special comments written in ``.bpl`` files (each file is an
individual test). These special comments (RUN lines) contain shell commands to
run. If any command exits with a non zero exit code the test is
considered to fail.

The RUN lines may use several substitutions

- ``%boogie`` expands to the absolute path to the Boogie executable with any set
  options and prefixed by ``mono`` on non Windows platforms. This does not need
  to be quoted.

- ``%diff`` expands to the diff tool being used. This is ``diff`` on non
  Windows platforms and ``pydiff`` on Windows. Do not use the ``fc`` tool
  because it is buggy when tests are run concurrently. This does not need to be
  quoted.

- ``%OutputCheck`` expands to the absolute path to the OutputCheck tool. This
  does not need to be quoted.

- ``%s`` the absolute path to the current test file. You should make sure this
  is quoted so that tests work correctly for users who use spaces in their file
  paths.

- ``%T`` the path to the temporary directory for this test. You should make sure
  this is quoted.

- ``%t`` expands to the absolute path of a filename that can be used as a
  temporary file. This always expands to the same value in a single test so if
  you need multiple different temporary files append a unique value (e.g.
  ``%t1``, ``%t2``... etc). You should make sure this is quoted.

Currently most tests simply execute boogie recording its output which then
compared to a file containing the expected output (``.expect`` files) using
``%diff``. This is incredibly fragile and it is recommended that new tests use
the OutputCheck tool instead of relying on %diff.

For more information see

http://llvm.org/docs/CommandGuide/lit.html
http://llvm.org/docs/TestingGuide.html#regression-test-structure
https://github.com/stp/OutputCheck/blob/master/README.md
