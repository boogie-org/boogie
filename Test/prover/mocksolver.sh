#!/bin/bash
while true ; do
    read cmd
    case $cmd in
      *get-info*name*   ) echo "(:name \"Z3\")" ;;
      *get-info*rlimit* ) echo "(:rlimit bad)" ;;
      *check-sat*       ) echo "unsat" ;;
      *                 ) continue ;;
    esac
done
