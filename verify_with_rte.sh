#!/usr/bin/env bash

NTRU_DIR=src/kem/ntru
NTRU_IMPL_DIR=$NTRU_DIR/pqclean_ntruhps4096821_clean

frama-c-gui -json-compilation-database compile_commands.json \
     -main PQCLEAN_NTRUHPS4096821_CLEAN_crypto_kem_keypair \
     -wp -rte -wp-rte \
     $NTRU_IMPL_DIR/kem.c \
     $NTRU_IMPL_DIR/owcpa.c \
     $NTRU_IMPL_DIR/poly.c \
     $NTRU_IMPL_DIR/sample.c
