#!/bin/bash
# Proves a check, and exits once it has answered the ping that follows the check's (pop 1).
while read -r line; do
  case "$line" in
    "(check-sat)") echo unsat ;;
    "(get-info :rlimit)") echo "(:rlimit 0)" ;;
    "(pop 1)") popped=1 ;;
    "(get-info :name)")
      echo '(:name "mock")'
      if [ -n "$popped" ]; then exit 0; fi ;;
  esac
done
