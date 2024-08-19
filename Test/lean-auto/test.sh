#!/bin/sh

set -e

boogie_file=$1
base=`basename $boogie_file .bpl`
lean_file="$base.lean"
dotnet ../../Source/BoogieDriver/bin/Debug/net6.0/BoogieDriver.dll /prune:1 /printLean:$lean_file $boogie_file
lake env lean $lean_file
