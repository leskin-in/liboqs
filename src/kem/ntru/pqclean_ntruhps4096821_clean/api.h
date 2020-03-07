#ifndef PQCLEAN_NTRUHPS4096821_CLEAN_API_H
#define PQCLEAN_NTRUHPS4096821_CLEAN_API_H

#include <stdint.h>

#define PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_SECRETKEYBYTES 1590
#define PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_PUBLICKEYBYTES 1230
#define PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_CIPHERTEXTBYTES 1230
#define PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_BYTES 32

#define PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_ALGNAME "ntruhps4096821"

int PQCLEAN_NTRUHPS4096821_CLEAN_crypto_kem_keypair(uint8_t *pk, uint8_t *sk);

/*@
    requires \valid_read (c + (0..1230));
    requires \valid_read (pk + (0..1230));
    requires \valid (k + (0..32));
    ensures \initialized (k + (0..32));
 */
int PQCLEAN_NTRUHPS4096821_CLEAN_crypto_kem_enc(uint8_t *c, uint8_t *k, const uint8_t *pk);

int PQCLEAN_NTRUHPS4096821_CLEAN_crypto_kem_dec(uint8_t *k, const uint8_t *c, const uint8_t *sk);

#endif
