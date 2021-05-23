#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "api.h"


typedef struct magic_s {
	uint8_t val[32];
} magic_t;


int main(void) {
	uint8_t *public_key = NULL;
	uint8_t *secret_key = NULL;
	uint8_t *ciphertext = NULL;
	uint8_t *shared_secret_e = NULL;
	uint8_t *shared_secret_d = NULL;
	int rc, ret = -1;
	int rv;

	//The magic numbers are 32 random values.
	//The length of the magic number was chosen arbitrarily to 32.
	magic_t magic = {{
			0xfa, 0xfa, 0xfa, 0xfa, 0xbc, 0xbc, 0xbc, 0xbc,
			0x15, 0x61, 0x15, 0x61, 0x15, 0x61, 0x15, 0x61,
			0xad, 0xad, 0x43, 0x43, 0xad, 0xad, 0x34, 0x34,
			0x12, 0x34, 0x56, 0x78, 0x12, 0x34, 0x56, 0x78
		}
	};

	public_key = malloc(PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_PUBLICKEYBYTES + sizeof(magic_t));
	secret_key = malloc(PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_SECRETKEYBYTES + sizeof(magic_t));
	ciphertext = malloc(PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_CIPHERTEXTBYTES + sizeof(magic_t));
	shared_secret_e = malloc(PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_BYTES + sizeof(magic_t));
	shared_secret_d = malloc(PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_BYTES + sizeof(magic_t));

	//Set the magic numbers
	memcpy(public_key + PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_PUBLICKEYBYTES, magic.val, sizeof(magic_t));
	memcpy(secret_key + PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_SECRETKEYBYTES, magic.val, sizeof(magic_t));
	memcpy(ciphertext + PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_CIPHERTEXTBYTES, magic.val, sizeof(magic_t));
	memcpy(shared_secret_e + PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_BYTES, magic.val, sizeof(magic_t));
	memcpy(shared_secret_d + PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_BYTES, magic.val, sizeof(magic_t));

	if ((public_key == NULL) || (secret_key == NULL) || (ciphertext == NULL) || (shared_secret_e == NULL) || (shared_secret_d == NULL)) {
		goto err;
	}

	rc = PQCLEAN_NTRUHPS4096821_CLEAN_crypto_kem_keypair(public_key, secret_key);
	if (rc != 0) {
		goto err;
	}

	rc = PQCLEAN_NTRUHPS4096821_CLEAN_crypto_kem_enc(ciphertext, shared_secret_e, public_key);
	if (rc != 0) {
		goto err;
	}

	rc = PQCLEAN_NTRUHPS4096821_CLEAN_crypto_kem_dec(shared_secret_d, ciphertext, secret_key);
	if (rc != 0) {
		goto err;
	}

	rv = memcmp(shared_secret_e, shared_secret_d, PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_BYTES);
	if (rv != 0) {
		goto err;
	}

	rv = memcmp(public_key + PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_PUBLICKEYBYTES, magic.val, sizeof(magic_t));
	rv |= memcmp(secret_key + PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_SECRETKEYBYTES, magic.val, sizeof(magic_t));
	rv |= memcmp(ciphertext + PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_CIPHERTEXTBYTES, magic.val, sizeof(magic_t));
	rv |= memcmp(shared_secret_e + PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_BYTES, magic.val, sizeof(magic_t));
	rv |= memcmp(shared_secret_d + PQCLEAN_NTRUHPS4096821_CLEAN_CRYPTO_BYTES, magic.val, sizeof(magic_t));
	if (rv != 0) {
		goto err;
	}

	ret = 0;
	goto cleanup;

err:
	ret = -1;

cleanup:
    free(secret_key);
    free(shared_secret_e);
    free(shared_secret_d);
	free(public_key);
	free(ciphertext);

	return ret;
}
