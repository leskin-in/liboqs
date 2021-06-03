#!/usr/bin/env bash

NTRU_DIR=src/kem/ntru
NTRU_IMPL_DIR=$NTRU_DIR/pqclean_ntruhps4096821_clean

frama-c-gui -json-compilation-database compile_commands.json \
     -main main \
     -rte -wp -wp-rte \
     $NTRU_IMPL_DIR/*
