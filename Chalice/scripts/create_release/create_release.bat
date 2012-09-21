@echo off
SetLocal

set BASE_DIR=%~dp0\..\..

set RELEASE_DIR_SRC=%~dp0\files
set RELEASE_DIR_DST=%~dp0\release

set CHALICE_JAR_SRC=%BASE_DIR%\target\scala-2.9.2\chalice_2.9.2-1.0.jar
set CHALICE_JAR_DST=%RELEASE_DIR_DST%\chalice.jar

pushd %BASE_DIR%
call sbt.bat package

popd

if exist "%RELEASE_DIR_DST%" rmdir /S /Q "%RELEASE_DIR_DST%"
mkdir "%RELEASE_DIR_DST%"

copy "%CHALICE_JAR_SRC%" "%CHALICE_JAR_DST%"
copy "%RELEASE_DIR_SRC%\*.*" "%RELEASE_DIR_DST%"
copy "%RELEASE_DIR_SRC%\*.*" "%RELEASE_DIR_DST%"

xcopy %BASE_DIR%\tests\examples %RELEASE_DIR_DST%\examples\