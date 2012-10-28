#!/bin/bash

CMDLINE="kwrite $1"

PLIST=`ps -Alf`

if echo "$PLIST" | grep -q -F "$CMDLINE"; then
    echo "File $1 is already open."
else
    sleep 5
    setsid nohup $CMDLINE &>/dev/null &
fi
