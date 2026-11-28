#!/bin/bash
# Stops reading as it answers the first ping, and then says nothing more for as long as Boogie runs.
while read -r line; do
  if [ "$line" = "(get-info :name)" ]; then
    exec 0<&-
    echo '(:name "mock")'
    while kill -0 "$PPID" 2>/dev/null; do sleep 0.1; done
    exit 0
  fi
done
