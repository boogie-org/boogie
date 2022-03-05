#!/bin/bash
if [ $# -lt 1 ]; then
    echo "Usage: test-with-params.sh <Boogie param> [additional lit params]"
    exit 1
fi

PARAM=$1
shift 1

DIR=Test
ALL_FILES=`lit $@ --show-tests ${DIR} | grep -v "Available Tests" | sed -e "s/  Boogie :: /${DIR}\//"`
TEST_FILES=`grep -L "SKIP-WITH-PARAM:.*${PARAM}" ${ALL_FILES}`

if [ -z "${PARAM}" ] ; then
  lit $@ Test
else
  lit $@ --param boogie_params="${PARAM}" ${TEST_FILES}
fi
