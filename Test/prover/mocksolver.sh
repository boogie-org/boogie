#!/bin/bash
while read cmd ; do
    case $cmd in
      *get-info*name*   ) echo "(:name \"Z3\")" ;;
      *get-info*rlimit* ) echo "(:rlimit bad)" ;;
      *get-info*reason-unknown* ) echo "incomplete" ;;
      *check-sat*       ) echo "unsat" ;;
      *get-model*       ) echo "(error \"model is not available\")" ;;
      *                 ) continue ;;
    esac
done
