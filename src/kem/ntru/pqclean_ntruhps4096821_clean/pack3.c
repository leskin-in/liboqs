#include "poly.h"

/*@
    requires \valid(msg + (0..((821 - 1) / 5 - 1)));
    requires \valid_read(a);
    requires \valid_read(a->coeffs + (0..(821 - 1)));
    assigns msg[0..(((821 - 1) / 5) - 1)];
*/
void PQCLEAN_NTRUHPS4096821_CLEAN_poly_S3_tobytes(unsigned char msg[NTRU_OWCPA_MSGBYTES], const poly *a) {
    int i;
    unsigned char c;

    /*@
        loop invariant 0 <= i <= (821 - 1) / 5;
        loop assigns msg[0..((821 - 1) / 5 - 1)];
        loop variant (821 - 1) / 5 - i;
    */
    for (i = 0; i < NTRU_PACK_DEG / 5; i++) {
        c =        a->coeffs[5 * i + 4] & 255;
        c = (3 * c + a->coeffs[5 * i + 3]) & 255;
        c = (3 * c + a->coeffs[5 * i + 2]) & 255;
        c = (3 * c + a->coeffs[5 * i + 1]) & 255;
        c = (3 * c + a->coeffs[5 * i + 0]) & 255;
        msg[i] = c;
    }
}

/*@
    requires \valid(r);
    requires \valid(r->coeffs + (0..(821 - 1)));
    requires \valid_read(msg + (0..(2 * (821 - 1 + 4) / 5)));
    assigns r->coeffs[0..(821 - 1)];
    ensures r->coeffs[821 - 1] == 0;
*/
void PQCLEAN_NTRUHPS4096821_CLEAN_poly_S3_frombytes(poly *r, const unsigned char msg[NTRU_OWCPA_MSGBYTES]) {
    int i;
    unsigned char c;

    /*@
        loop invariant 0 <= i <= (821 - 1) / 5;
        loop assigns i, r->coeffs[0..(821 - 1 - 1)];
        loop variant (821 - 1) / 5 - i;
    */
    for (i = 0; i < NTRU_PACK_DEG / 5; i++) {
        c = msg[i];
        r->coeffs[5 * i + 0] = c;
        r->coeffs[5 * i + 1] = c * 171 >> 9; // this is division by 3
        r->coeffs[5 * i + 2] = c * 57 >> 9; // division by 3^2
        r->coeffs[5 * i + 3] = c * 19 >> 9; // division by 3^3
        r->coeffs[5 * i + 4] = c * 203 >> 14; // etc.
    }
    r->coeffs[NTRU_N - 1] = 0;
    PQCLEAN_NTRUHPS4096821_CLEAN_poly_mod_3_Phi_n(r);
}

