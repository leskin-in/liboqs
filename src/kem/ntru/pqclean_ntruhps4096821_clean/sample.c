#include "sample.h"

/*@
    requires \valid_read(uniformbytes + (0..(821 - 1 + (30 * (821 - 1) + 7) / 8 - 1)));
    requires \valid(f);
    requires \valid(g);
    requires \valid (f->coeffs + (0..(821 - 1)));
    requires \valid (g->coeffs + (0..(821 - 1)));
    requires \forall integer i; 0 <= i <= (821 - 1 + (30 * (821 - 1) + 7) / 8 - 1) ==> 0 <= uniformbytes[i] <= 65535;

    ensures \forall integer i; 0 <= i < (821 - 1) ==> 0 <= f->coeffs[i] <= 2;
    ensures f->coeffs[821 - 1] == 0;
    ensures \forall integer i; 0 <= i < (821 - 1) ==> 0 <= g->coeffs[i] <= 2;
    ensures g->coeffs[821 - 1] == 0;

    assigns f->coeffs[0..(821 - 1)];
    assigns g->coeffs[0..(821 - 1)];
 */ 
void PQCLEAN_NTRUHPS4096821_CLEAN_sample_fg(poly *f, poly *g, const unsigned char uniformbytes[NTRU_SAMPLE_FG_BYTES]) {

    PQCLEAN_NTRUHPS4096821_CLEAN_sample_iid(f, uniformbytes);
    PQCLEAN_NTRUHPS4096821_CLEAN_sample_fixed_type(g, uniformbytes + NTRU_SAMPLE_IID_BYTES);
}

/*@
    requires \valid_read(uniformbytes + (0..(821 - 1 + (30 * (821 - 1) + 7) / 8 - 1)));
    requires \valid(r);
    requires \valid(m);
    requires \valid (r->coeffs + (0..(821 - 1)));
    requires \valid (m->coeffs + (0..(821 - 1)));
    requires \forall integer i; 0 <= i <= (821 - 1 + (30 * (821 - 1) + 7) / 8 - 1) ==> 0 <= uniformbytes[i] <= 65535;

    ensures \forall integer i; 0 <= i < (821 - 1) ==> 0 <= r->coeffs[i] <= 2;
    ensures r->coeffs[821 - 1] == 0;

    assigns r->coeffs[0..(821 - 1)];
    assigns m->coeffs[0..(821 - 1)];
 */ 
void PQCLEAN_NTRUHPS4096821_CLEAN_sample_rm(poly *r, poly *m, const unsigned char uniformbytes[NTRU_SAMPLE_RM_BYTES]) {

    PQCLEAN_NTRUHPS4096821_CLEAN_sample_iid(r, uniformbytes);
    PQCLEAN_NTRUHPS4096821_CLEAN_sample_fixed_type(m, uniformbytes + NTRU_SAMPLE_IID_BYTES);
}


/*@
    requires \valid_read(u + (0..((30 * (821 - 1) + 7) / 8)));
    requires \valid(r->coeffs + (0..(821 - 1)));
    
    ensures \forall integer i; 0 <= i < (821 - 1) ==> 0 <= r->coeffs[i] <= 3;
    ensures r->coeffs[821 - 1] == 0;

    assigns r->coeffs[0..(821 - 1)];
 */
void PQCLEAN_NTRUHPS4096821_CLEAN_sample_fixed_type(poly *r, const unsigned char u[NTRU_SAMPLE_FT_BYTES]) {
    // Assumes NTRU_SAMPLE_FT_BYTES = ceil(30*(n-1)/8)

    int32_t s[NTRU_N - 1];
    int i;

    // Use 30 bits of u per word
    /*@
        loop invariant 0 <= i <= (821 - 1) / 4;
        loop invariant \forall size_t j; 0 <= j < (i * 4) ==> \initialized(s + j);
        loop assigns i;
        loop assigns s[0..821 - 1];
        loop variant ((821 - 1) / 4 - i);
    */
    for (i = 0; i < (NTRU_N - 1) / 4; i++) {
        s[4 * i + 0] =                              (u[15 * i + 0] << 2) + (u[15 * i + 1] << 10) + (u[15 * i + 2] << 18) + ((uint32_t) u[15 * i + 3] << 26);
        s[4 * i + 1] = ((u[15 * i + 3] & 0xc0) >> 4) + (u[15 * i + 4] << 4) + (u[15 * i + 5] << 12) + (u[15 * i + 6] << 20) + ((uint32_t) u[15 * i + 7] << 28);
        s[4 * i + 2] = ((u[15 * i + 7] & 0xf0) >> 2) + (u[15 * i + 8] << 6) + (u[15 * i + 9] << 14) + (u[15 * i + 10] << 22) + ((uint32_t) u[15 * i + 11] << 30);
        s[4 * i + 3] =  (u[15 * i + 11] & 0xfc)       + (u[15 * i + 12] << 8) + (u[15 * i + 13] << 16) + ((uint32_t) u[15 * i + 14] << 24);
    }

    /*@
        loop invariant 0 <= i <= ((1 << 12) / 8 - 2) / 2;
        loop assigns i;
        loop assigns s[0..(((1 << 12) / 8 - 2) / 2 - 1)];
        loop variant (((1 << 12) / 8 - 2) / 2 - i);
    */
    for (i = 0; i < NTRU_WEIGHT / 2; i++) {
        s[i] |=  1;
    }

    /*@
        loop invariant ((1 << 12) / 8 - 2) / 2 <= i <= ((1 << 12) / 8 - 2);
        loop assigns i;
        loop assigns s[(((1 << 12) / 8 - 2) / 2)..(((1 << 12) / 8 - 2) - 1)];
        loop variant (((1 << 12) / 8 - 2) - i);
    */
    for (i = NTRU_WEIGHT / 2; i < NTRU_WEIGHT; i++) {
        s[i] |=  2;
    }

    PQCLEAN_NTRUHPS4096821_CLEAN_crypto_sort_int32(s, NTRU_N - 1);

    for (i = 0; i < NTRU_N - 1; i++) {
        r->coeffs[i] = ((uint16_t) (s[i] & 3));
    }

    r->coeffs[NTRU_N - 1] = 0;
}
