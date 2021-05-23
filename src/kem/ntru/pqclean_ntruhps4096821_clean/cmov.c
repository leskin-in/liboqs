#include "cmov.h"

/* b = 1 means mov, b = 0 means don't mov*/
/*@
    requires \valid(r + (0..(len - 1)));
    requires \valid_read(x + (0..(len - 1)));
    assigns r[0..(len - 1)];
*/
void PQCLEAN_NTRUHPS4096821_CLEAN_cmov(unsigned char *r, const unsigned char *x, size_t len, unsigned char b) {
    size_t i;

    b = (~b + 1);
    /*@
        loop invariant 0 <= i <= len;
        loop assigns r[0..(len - 1)];
        loop variant len - i;
    */
    for (i = 0; i < len; i++) {
        r[i] ^= b & (x[i] ^ r[i]);
    }
}
