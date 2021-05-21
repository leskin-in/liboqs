/* Based on supercop-20200702/crypto_core/invhrss701/simpler/core.c */

#include "poly.h"

/* return -1 if x<0 and y<0; otherwise return 0 */
/*@
    axiomatic Both_negative {
        logic short both_negative_mask(short x, short y) reads \nothing;
        axiom both_negative_negative:
            \forall short x, y; (x < 0 && y < 0) ==> (both_negative_mask(x, y) != 0);
        axiom both_negative_not_negative:
            \forall short x, y; (x >= 0 || y >= 0) ==> (both_negative_mask(x, y) == 0);
    }
*/
/*@
    ensures \result == both_negative_mask(x, y);
    assigns \nothing;
*/
static inline int16_t both_negative_mask(int16_t x, int16_t y) {
    return (x & y) >> 15;
}

/*@
    requires \valid(r);
    requires \valid(r->coeffs + (0..(821 - 1)));
    requires \valid_read(a);
    requires \valid_read(a->coeffs + (0..(821 - 1)));
    assigns r->coeffs[0..(821 - 1)];
    ensures \initialized(r->coeffs + (0..(821 - 1)));
*/
void PQCLEAN_NTRUHPS4096821_CLEAN_poly_R2_inv(poly *r, const poly *a) {
    poly f, g, v, w;
    size_t i, loop;
    int16_t delta, sign, swap, t;

    /*@
        loop invariant 0 <= i <= 821;
        loop invariant \forall integer j; (0 <= j < i) ==> (v.coeffs[j] == 0);
        loop assigns i, v.coeffs[0..(821 - 1)];
        loop variant 821 - i;
    */
    for (i = 0; i < NTRU_N; ++i) {
        v.coeffs[i] = 0;
    }
    /*@
        loop invariant 0 <= i <= 821;
        loop invariant \forall integer j; (0 <= j < i) ==> (w.coeffs[j] == 0);
        loop assigns i, w.coeffs[0..(821 - 1)];
        loop variant 821 - i;
    */
    for (i = 0; i < NTRU_N; ++i) {
        w.coeffs[i] = 0;
    }
    w.coeffs[0] = 1;

    /*@
        loop invariant 0 <= i <= 821;
        loop invariant \forall integer j; (0 <= j < i) ==> (f.coeffs[j] == 1);
        loop assigns i, f.coeffs[0..(821 - 1)];
        loop variant 821 - i;
    */
    for (i = 0; i < NTRU_N; ++i) {
        f.coeffs[i] = 1;
    }
    /*@
        loop invariant 0 <= i <= 821 - 1;
        loop assigns i, g.coeffs[0..(821 - 2)];
        loop variant 821 - 1 - i;
    */
    for (i = 0; i < NTRU_N - 1; ++i) {
        g.coeffs[NTRU_N - 2 - i] = (a->coeffs[i] ^ a->coeffs[NTRU_N - 1]) & 1;
    }
    g.coeffs[NTRU_N - 1] = 0;

    delta = 1;

    /*@
        loop invariant 0 <= loop <= 2 * (821 - 1) - 1;
        loop assigns loop, sign, swap, delta, t, v.coeffs[0..(821 - 1)], f.coeffs[0..(821 - 1)], g.coeffs[0..(821 - 1)], w.coeffs[0..(821 - 1)];
        loop variant 2 * (821 - 1) - 1 - loop;
    */
    for (loop = 0; loop < 2 * (NTRU_N - 1) - 1; ++loop) {
        /*@
            loop invariant 0 <= i <= 821 - 1;
            loop assigns i, v.coeffs[1..(821 - 1)];
            loop variant i;
        */
        for (i = NTRU_N - 1; i > 0; --i) {
            v.coeffs[i] = v.coeffs[i - 1];
        }
        v.coeffs[0] = 0;

        sign = g.coeffs[0] & f.coeffs[0];
        swap = both_negative_mask(-delta, -(int16_t) g.coeffs[0]);
        delta ^= swap & (delta ^ -delta);
        delta += 1;

        /*@
            loop invariant 0 <= i <= 821;
            loop assigns i, t, f.coeffs[0..(821 - 1)], g.coeffs[0..(821 - 1)], v.coeffs[0..(821 - 1)], w.coeffs[0..(821 - 1)];
            loop variant 821 - i;
        */
        for (i = 0; i < NTRU_N; ++i) {
            t = swap & (f.coeffs[i] ^ g.coeffs[i]);
            f.coeffs[i] ^= t;
            g.coeffs[i] ^= t;
            t = swap & (v.coeffs[i] ^ w.coeffs[i]);
            v.coeffs[i] ^= t;
            w.coeffs[i] ^= t;
        }

        /*@
            loop invariant 0 <= i <= 821;
            loop assigns i, g.coeffs[0..(821 - 1)];
            loop variant 821 - i;
        */
        for (i = 0; i < NTRU_N; ++i) {
            g.coeffs[i] = g.coeffs[i] ^ (sign & f.coeffs[i]);
        }
        /*@
            loop invariant 0 <= i <= 821;
            loop assigns i, w.coeffs[0..(821 - 1)];
            loop variant 821 - i;
        */
        for (i = 0; i < NTRU_N; ++i) {
            w.coeffs[i] = w.coeffs[i] ^ (sign & v.coeffs[i]);
        }
        /*@
            loop invariant 0 <= i <= 821 - 1;
            loop assigns i, g.coeffs[0..(821 - 1 - 1)];
            loop variant 821 - 1 - i;
        */
        for (i = 0; i < NTRU_N - 1; ++i) {
            g.coeffs[i] = g.coeffs[i + 1];
        }
        g.coeffs[NTRU_N - 1] = 0;
    }

    /*@
        loop invariant 0 <= i <= 821 - 1;
        loop assigns i, r->coeffs[0..(821 - 1 - 1)];
        loop variant 821 - 1 - i;
    */
    for (i = 0; i < NTRU_N - 1; ++i) {
        r->coeffs[i] = v.coeffs[NTRU_N - 2 - i];
    }
    r->coeffs[NTRU_N - 1] = 0;
}
