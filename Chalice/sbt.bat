@ECHO OFF
SetLocal

set SCRIPT_DIR=%~dp0
java %JAVA_OPTS% -XX:MaxPermSize=256m -Xmx512M -Xss2M -jar "%SCRIPT_DIR%sbt-launch.jar" %*
