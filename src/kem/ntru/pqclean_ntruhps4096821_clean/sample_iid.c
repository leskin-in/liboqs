#include "sample.h"

/*@
    requires type_bounds: 0 <= a <= 65535;
    ensures (0 <= \result <= 2);
    ensures (\result == a % 3);
    assigns \nothing;
 */
static uint16_t mod3(uint16_t a) {
    uint16_t r;
    int16_t t, c;

    r = (a >> 8) + (a & 0xff); // r mod 255 == a mod 255
    r = (r >> 4) + (r & 0xf); // r' mod 15 == r mod 15
    r = (r >> 2) + (r & 0x3); // r' mod 3 == r mod 3
    r = (r >> 2) + (r & 0x3); // r' mod 3 == r mod 3

    t = r - 3;
    c = t >> 15;

    return (c & r) ^ (~c & t);
}

/*@
    requires \valid (r);
    requires \valid (r->coeffs + (0..(821 - 1)));
    requires \valid_read (uniformbytes + (0..(821 - 1 - 1)));
    requires \forall integer i; 0 <= i <= (821 - 1 - 1) ==> 0 <= uniformbytes[i] <= 65535;
    ensures \forall integer i; 0 <= i < (821 - 1) ==> 0 <= r->coeffs[i] <= 2;
    ensures r->coeffs[821 - 1] == 0;
    assigns r->coeffs[0..(821 - 1)];
 */
void PQCLEAN_NTRUHPS4096821_CLEAN_sample_iid(poly *r, const unsigned char uniformbytes[NTRU_SAMPLE_IID_BYTES]) {
    int i;
    /* {0,1,...,255} -> {0,1,2}; Pr[0] = 86/256, Pr[1] = Pr[-1] = 85/256 */
    /*@
        loop invariant 0 <= i <= 821 - 1 - 1;
        loop assigns i, r->coeffs[0..821 - 1 - 1];
    */
    for (i = 0; i < NTRU_N - 1; i++) {
        r->coeffs[i] = mod3(uniformbytes[i]);
    }

    r->coeffs[NTRU_N - 1] = 0;
}
