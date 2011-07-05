
Chalice Test Suite
==================

Contents
--------
- examples: Various examples how Chalice can be used to verify concurrent
  programs.
- permission-model: Regression tests for the permission model of Chalice.
- refinements: Regression tests for the refinement extension.
- test-scripts: Some batch scripts that can be used to execute the tests in an
  easy and automated way. More information below.


Test Scripts
------------
In the directory test-scripts are various scripts to allow the execution of the
tests in different ways. There are launchers in the test directories (e.g. in
examples or permission-model) to access them.

Commands (sorted by relevance):
- test.bat <file> [-params]: Execute a test and output the result of the
  verification. Note: <file> must not include the file extension.
- reg_test.bat <file> [-params]: Execute a tests as a regression test, i.e., run
  the test and compare the verification result with the reference output stored
  in <file.output.txt>. Also shows the differences if any.
- reg_test_all.bat: Execute all tests as regression tests in the current
  directory.
- generete_reference.bat <file> [-params]: Generate the reference output.
- generate_reference_all.bat: Generate reference files for all tests in the
  current directory.
- getboogieoutput.bat: File used internally by generete_reference.bat.

To provide additional parameters to Chalice when verifying the tests (e.g., to
test the autoMagic feature, see tests/examples/RockBand-automagic.chalice), one
can start the Chalice source file with the line
  "// chalice-parameter=<list of space-separated parameters>"

Note: For the refinement tests, there is a bash script test.sh.
