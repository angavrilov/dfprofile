#!/bin/bash

CMDLINE="kwrite --caption CFG --geometry 500x300 $1"

PLIST=`ps -Alf`

if echo "$PLIST" | grep -q -F "$CMDLINE"; then
    echo "File $1 is already open."
else
    setsid nohup $CMDLINE &>/dev/null &
fi
