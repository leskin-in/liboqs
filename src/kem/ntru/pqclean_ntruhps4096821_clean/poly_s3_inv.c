/* Based on supercop-20200702/crypto_core/invhrss701/simpler/core.c */

/*@
    axiomatic Mod3_short {
        logic short mod3_short(short a) reads \nothing;
        axiom mod3_short_axiom_in_bounds:
            \forall short n, r; (0 <= n <= 256 && mod3_short(n) == r) ==> \false;
        axiom mod3_short_is_correct_in_bounds:
            \forall short n; 0 <= n <= 256 ==> mod3_short(n) == n % 3;
        axiom mod3_short_is_bounded_in_bounds:
            \forall short n; 0 <= n <= 256 ==> 0 <= mod3_short(n) <= 2;

    }
*/

#include "poly.h"

/*@
    requires type_bounds: 0 <= a <= 9;
    ensures \result == mod3_short(a);
    assigns \nothing;
 */
static inline uint8_t mod3(uint8_t a) { /* a between 0 and 9 */
    int16_t t, c;
    a = (a >> 2) + (a & 3); /* between 0 and 4 */
    t = a - 3;
    c = t >> 5;
    return (uint8_t) (t ^ (c & (a ^ t)));
}

/* return -1 if x<0 and y<0; otherwise return 0 */
/*@
    behavior both_negative:
        assumes x < 0 && y < 0;
        ensures \result == -1;

    behavior some_not_negitive:
        assumes !(x < 0 && y < 0);
        ensures \result == 0;

    complete behaviors;
    disjoint behaviors;
*/
static inline int16_t both_negative_mask(int16_t x, int16_t y) {
    return (x & y) >> 15;
}

/*@
    requires \valid(r);
    requires \valid_read(a);

    ensures \forall integer i; 0 <= i < (821 - 1) ==> 0 <= r->coeffs[i] <= 3;

    assigns r->coeffs[0..(821 - 1)];
 */
void PQCLEAN_NTRUHPS4096821_CLEAN_poly_S3_inv(poly *r, const poly *a) {
    poly f, g, v, w;
    size_t i, loop;
    int16_t delta, sign, swap, t;

    /*@
        loop invariant 0 <= i <= 821;
        loop invariant \forall size_t j; 0 <= j < i ==> v.coeffs[j] == 0;
        loop assigns i;
        loop assigns v.coeffs[0..821 - 1];
        loop variant 821 - i;
    */
    for (i = 0; i < NTRU_N; ++i) {
        v.coeffs[i] = 0;
    }
    /*@
        loop invariant 0 <= i <= 821;
        loop invariant \forall size_t j; 0 <= j < i ==> w.coeffs[j] == 0;
        loop assigns i;
        loop assigns w.coeffs[0..821 - 1];
        loop variant 821 - i;
    */
    for (i = 0; i < NTRU_N; ++i) {
        w.coeffs[i] = 0;
    }
    w.coeffs[0] = 1;

    /*@
        loop invariant 0 <= i <= 821;
        loop invariant \forall size_t j; 0 <= j < i ==> f.coeffs[j] == 1;
        loop assigns i;
        loop assigns f.coeffs[0..821 - 1];
        loop variant 821 - i;
    */
    for (i = 0; i < NTRU_N; ++i) {
        f.coeffs[i] = 1;
    }
    /*@
        loop invariant 0 <= i <= 821 - 1;
        loop invariant \forall size_t j; 821 - 2 - i <= j < 821 - 1 ==> 0 <= g.coeffs[j] < 7;
        loop assigns i;
        loop assigns g.coeffs[0..821 - 1];
        loop variant 821 - i;
    */
    for (i = 0; i < NTRU_N - 1; ++i) {
        g.coeffs[NTRU_N - 2 - i] = mod3((a->coeffs[i] & 3) + 2 * (a->coeffs[NTRU_N - 1] & 3));
    }
    g.coeffs[NTRU_N - 1] = 0;

    delta = 1;

    /*@
        loop invariant 0 <= loop <= 2 * (821 - 1) - 1;
        loop assigns loop;
        loop assigns v.coeffs[0..821 - 1];
        loop assigns g.coeffs[0..821 - 1];
        loop assigns w.coeffs[0..821 - 1];
        loop assigns delta, sign, swap, t;
        loop variant 2 * (821 - 1) - 1 - loop;
    */
    for (loop = 0; loop < 2 * (NTRU_N - 1) - 1; ++loop) {
        /*@
            loop invariant 0 <= i <= 821 - 1;
            loop assigns i;
            loop assigns v.coeffs[1..821 - 1];
            loop variant i;
        */
        for (i = NTRU_N - 1; i > 0; --i) {
            v.coeffs[i] = v.coeffs[i - 1];
        }
        v.coeffs[0] = 0;

        sign = mod3((uint8_t) (2 * g.coeffs[0] * f.coeffs[0]));
        swap = both_negative_mask(-delta, -(int16_t) g.coeffs[0]);
        delta ^= swap & (delta ^ -delta);
        delta += 1;

        /*@
            loop invariant 0 <= i <= 821;
            loop assigns i, t;
            loop assigns f.coeffs[0..821 - 1];
            loop assigns g.coeffs[0..821 - 1];
            loop assigns v.coeffs[0..821 - 1];
            loop assigns w.coeffs[0..821 - 1];
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
            loop invariant \forall size_t j; 0 <= j < i ==> g.coeffs[j] < 3;
            loop assigns i;
            loop assigns g.coeffs[0..821 - 1];
            loop variant 821 - i;
        */
        for (i = 0; i < NTRU_N; ++i) {
            g.coeffs[i] = mod3((uint8_t) (g.coeffs[i] + sign * f.coeffs[i]));
        }
        /*@
            loop invariant 0 <= i <= 821;
            loop invariant \forall size_t j; 0 <= j < i ==> w.coeffs[j] < 3;
            loop assigns i;
            loop assigns w.coeffs[0..821 - 1];
            loop variant 821 - i;
        */
        for (i = 0; i < NTRU_N; ++i) {
            w.coeffs[i] = mod3((uint8_t) (w.coeffs[i] + sign * v.coeffs[i]));
        }
        /*@
            loop invariant 0 <= i <= 821 - 1;
            loop assigns i;
            loop assigns g.coeffs[0..821 - 2];
            loop variant 821 - i;
        */
        for (i = 0; i < NTRU_N - 1; ++i) {
            g.coeffs[i] = g.coeffs[i + 1];
        }
        g.coeffs[NTRU_N - 1] = 0;
    }

    sign = f.coeffs[0];
    
    /*@
        loop invariant 0 <= i <= 821 - 1;
        loop invariant \forall size_t j; 0 <= j < i ==> w.coeffs[j] < 3;
        loop assigns i;
        loop assigns r->coeffs[0..821 - 1];
        loop variant 821 - 1 - i;
    */
    for (i = 0; i < NTRU_N - 1; ++i) {
        r->coeffs[i] = mod3((uint8_t) (sign * v.coeffs[NTRU_N - 2 - i]));
    }
    r->coeffs[NTRU_N - 1] = 0;
}
