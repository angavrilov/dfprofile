#!/bin/bash

rm Dwarf_Fortress.*
touch Dwarf_Fortress.func_names
rm -f *.dot *.svg *.stack log.*

./callgraph.pl
./disasm.sh
