
Chalice - Verification of Concurrent Software
=============================================

Compiling Chalice: sbt compile
Running Chalice: chalice.bat <file.chalice> [-params]
  By default, chalice looks for Boogie in C:\Boogie\Binaries. If your
  Boogie executable is located elsewhere, you can edit chalice.bat
  to indicate the appropriate location such as 
    REM Chalice command line options
    set CHALICE_OPTS=/boogie:"C:\Boogie-CodePlex\Binaries\Boogie.exe"
Running the tests for Chalice: see tests/readme.txt

Chalice is built using Simple Build Tool (https://github.com/harrah/xsbt/wiki/Setup)

Note: You might have to increase the stack size of the JVM to avoid a stack
overflow, for instance by changing scala.bat by adding "-Xss16M" to the
JAVA_OPTS: 
    if "%_JAVA_OPTS%"=="" set _JAVA_OPTS=-Xmx256M -Xms32M -Xss16M
