
Chalice - Verification of Concurrent Software
=============================================

Compiling Chalice: sbt compile
Running Chalice: chalice.bat <file.chalice> [-params]
Running the tests for Chalice: see tests/readme.txt

Chalice is built using Simple Build Tool (https://github.com/harrah/xsbt/wiki/Setup)

Note: You might have to increase the stack size of the JVM to avoid a stack
overflow, for instance by changing scala.bat by adding "-Xss16M" to the
JAVA_OPTS: 
    if "%_JAVA_OPTS%"=="" set _JAVA_OPTS=-Xmx256M -Xms32M -Xss16M
