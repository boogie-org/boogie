#!/bin/sh

if [ -e /cygdrive/c/Python27/python.exe ] ; then
  PYTHON=/cygdrive/c/Python27/python
else
  PYTHON=python
fi

CONF=$1
CONF=${CONF:=Debug}

$PYTHON ../lit/lit.py -sv --param configuration=$CONF .
