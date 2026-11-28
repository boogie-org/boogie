#!/bin/bash
# Proves the check, and stops reading once it has answered everything Boogie asks about it.
while read -r line; do
  case "$line" in
    "(check-sat)") echo unsat ;;
    "(get-info :rlimit)") echo "(:rlimit 0)"; answered=1 ;;
    "(get-info :name)")
      if [ -n "$answered" ]; then exec 0<&-; fi
      echo '(:name "mock")'
      if [ -n "$answered" ]; then exit 0; fi ;;
  esac
done
