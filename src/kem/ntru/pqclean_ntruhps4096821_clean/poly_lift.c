#include "poly.h"

/*@
    requires \valid(r);
    requires \valid(r->coeffs + (0..(821 - 1)));
    requires \valid_read(a);
    requires \valid_read(a->coeffs + (0..(821 - 1)));
    assigns r->coeffs[0..(821 - 1)];
*/
void PQCLEAN_NTRUHPS4096821_CLEAN_poly_lift(poly *r, const poly *a) {
    int i;
    /*@
        loop invariant 0 <= i <= 821;
        loop assigns i, r->coeffs[0..(821 - 1)];
        loop variant 821 - i;
    */
    for (i = 0; i < NTRU_N; i++) {
        r->coeffs[i] = a->coeffs[i];
    }
    PQCLEAN_NTRUHPS4096821_CLEAN_poly_Z3_to_Zq(r);
}


