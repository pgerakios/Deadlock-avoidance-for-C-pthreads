#!/bin/sh

vanilla=`cat OUTPUT.vanilla | awk '\
  BEGIN      { counts = 0; user = 0; syst = 0; elapsed = 0; } \
  /Counts =/ { counts += $7; } \
  /user/     { user += $2; syst += $3; elapsed += $4; } \
  END        { printf "%d %0.2f %0.2f %0.2f %0.2f", \
                 counts, user, syst, elapsed, (counts / elapsed); }'`

printf "vanilla:\t$vanilla\n"

modified=`cat OUTPUT.modified | awk '\
  BEGIN      { counts = 0; user = 0; syst = 0; elapsed = 0; } \
  /Counts =/ { counts += $7; } \
  /user/     { user += $2; syst += $3; elapsed += $4; } \
  END        { printf "%d %0.2f %0.2f %0.2f %0.2f", \
                 counts, user, syst, elapsed, (counts / elapsed); }'`

printf "modified:\t$modified\n"
