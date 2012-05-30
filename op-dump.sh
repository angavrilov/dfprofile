#!/bin/bash

DFPATH=../df_linux

if [ -n "$1" ]; then
    DFPATH="$1"
fi

opcontrol --dump 1>&2
opreport -ld $DFPATH/libs/Dwarf_Fortress
