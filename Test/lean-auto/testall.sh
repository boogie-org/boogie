#!/bin/sh

set -e

for test in `cat lean-tests` ; do
  ./test.sh $test
done
