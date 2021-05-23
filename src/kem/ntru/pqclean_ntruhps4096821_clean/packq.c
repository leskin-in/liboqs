#include "poly.h"


/*@
    requires \valid(r + (0..(3 * ((821 - 1) / 2) - 1)));
    requires \valid_read(a);
    requires \valid_read(a->coeffs + (0..(821 - 1)));
    assigns r[0..(3 * ((821 - 1) / 2) - 1)];
*/
void PQCLEAN_NTRUHPS4096821_CLEAN_poly_Sq_tobytes(unsigned char *r, const poly *a) {
    int i;

    /*@
        loop invariant 0 <= i <= ((821 - 1) / 2);
        loop assigns r[0..(3 * ((821 - 1) / 2) - 1)];
        loop variant ((821 - 1) / 2) - i;
    */
    for (i = 0; i < NTRU_PACK_DEG / 2; i++) {
        r[3 * i + 0] = (unsigned char) ( MODQ(a->coeffs[2 * i + 0]) & 0xff);
        r[3 * i + 1] = (unsigned char) ((MODQ(a->coeffs[2 * i + 0]) >>  8) | ((MODQ(a->coeffs[2 * i + 1]) & 0x0f) << 4));
        r[3 * i + 2] = (unsigned char) ((MODQ(a->coeffs[2 * i + 1]) >>  4));
    }
}

/*@
    requires \valid(r);
    requires \valid(r->coeffs + (0..(821 - 1)));
    requires \valid_read(a + (0..(3 * ((821 - 1) / 2) - 1)));
    assigns r->coeffs[0..(821 - 1)];
    ensures r->coeffs[821 - 1] == 0;
*/
void PQCLEAN_NTRUHPS4096821_CLEAN_poly_Sq_frombytes(poly *r, const unsigned char *a) {
    int i;
    /*@
        loop invariant 0 <= i <= ((821 - 1)/ 2);
        loop assigns i, r->coeffs[0..(821 - 1 - 1)];
        loop variant ((821 - 1) / 2) - i;
    */
    for (i = 0; i < NTRU_PACK_DEG / 2; i++) {
        r->coeffs[2 * i + 0] = (a[3 * i + 0] >> 0) | (((uint16_t)a[3 * i + 1] & 0x0f) << 8);
        r->coeffs[2 * i + 1] = (a[3 * i + 1] >> 4) | (((uint16_t)a[3 * i + 2] & 0xff) << 4);
    }
    r->coeffs[NTRU_N - 1] = 0;
}

/*@
    requires \valid(r + (0..(3 * ((821 - 1) / 2) - 1)));
    requires \valid_read(a->coeffs + (0..(821 - 1)));
    assigns r[0..(3 * ((821 - 1) / 2) - 1)];
*/
void PQCLEAN_NTRUHPS4096821_CLEAN_poly_Rq_sum_zero_tobytes(unsigned char *r, const poly *a) {
    PQCLEAN_NTRUHPS4096821_CLEAN_poly_Sq_tobytes(r, a);
}

/*@
    requires \valid(r);
    requires \valid(r->coeffs + (0..(821 - 1)));
    requires \valid_read(a + (0..(3 * ((821 - 1) / 2) - 1)));
    assigns r->coeffs[0..(821 - 1)];
*/
void PQCLEAN_NTRUHPS4096821_CLEAN_poly_Rq_sum_zero_frombytes(poly *r, const unsigned char *a) {
    int i;
    PQCLEAN_NTRUHPS4096821_CLEAN_poly_Sq_frombytes(r, a);

    /* Set r[n-1] so that the sum of coefficients is zero mod q */
    r->coeffs[NTRU_N - 1] = 0;
    /*@
        loop invariant 0 <= i <= (821 - 1);
        loop assigns i, r->coeffs[0..(821 - 1 - 1)];
        loop variant 821 - 1 - i;
    */
    for (i = 0; i < NTRU_PACK_DEG; i++) {
        r->coeffs[NTRU_N - 1] -= r->coeffs[i];
    }
}
