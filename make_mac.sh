#!/bin/sh
# Utility to run the makefile from the commandline based on the default MacOSX installation
# Call with the same arguments as `make`

export COQLIBS="-coqlib /Applications/CoqIdE_8.4.app/Contents/Resources/lib/coq -I ."
export COQDOCLIBS="-coqlib /Applications/CoqIdE_8.4.app/Contents/Resources/lib/coq"

make $*
