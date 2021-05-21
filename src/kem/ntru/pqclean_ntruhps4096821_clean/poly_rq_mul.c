#include "poly.h"

/* Polynomial multiplication using     */
/* Toom-4 and two layers of Karatsuba. */

#define L PAD32(NTRU_N)
#define M (L/4)
#define K (L/16)

static void toom4_k2x2_mul(uint16_t ab[2 * L], const uint16_t a[L], const uint16_t b[L]);

static void toom4_k2x2_eval_0(uint16_t r[9 * K], const uint16_t a[M]);
static void toom4_k2x2_eval_p1(uint16_t r[9 * K], const uint16_t a[M]);
static void toom4_k2x2_eval_m1(uint16_t r[9 * K], const uint16_t a[M]);
static void toom4_k2x2_eval_p2(uint16_t r[9 * K], const uint16_t a[M]);
static void toom4_k2x2_eval_m2(uint16_t r[9 * K], const uint16_t a[M]);
static void toom4_k2x2_eval_p3(uint16_t r[9 * K], const uint16_t a[M]);
static void toom4_k2x2_eval_inf(uint16_t r[9 * K], const uint16_t a[M]);
static inline void k2x2_eval(uint16_t r[9 * K]);

static void toom4_k2x2_basemul(uint16_t r[18 * K], const uint16_t a[9 * K], const uint16_t b[9 * K]);
static inline void schoolbook_KxK(uint16_t r[2 * K], const uint16_t a[K], const uint16_t b[K]);

static void toom4_k2x2_interpolate(uint16_t r[2 * M], const uint16_t a[63 * 2 * K]);
static inline void k2x2_interpolate(uint16_t r[M], const uint16_t a[9 * K]);

/*@
    requires \valid_read(a);
    requires \valid_read(a->coeffs + (0..(821 - 1)));
    requires \valid_read(b);
    requires \valid_read(b->coeffs + (0..(821 - 1)));
    requires \valid(r);
    requires \valid(r->coeffs + (0..(821 - 1)));
    assigns r->coeffs[0..(821 - 1)];
    ensures \initialized(r->coeffs + (0..(821 - 1)));
*/
void PQCLEAN_NTRUHPS4096821_CLEAN_poly_Rq_mul(poly *r, const poly *a, const poly *b) {
    size_t i;
    uint16_t ab[2 * L];

    /*@
        loop invariant 0 <= i <= 821;
        loop assigns (ab[0..(821 - 1)]), (ab[(832)..(832 + 821 - 1)]);
        loop variant 821 - i;
    */
    for (i = 0; i < NTRU_N; i++) {
        ab[i] = a->coeffs[i];
        ab[L + i] = b->coeffs[i];
    }
    /*@
        loop invariant 821 <= i <= 832;
        loop assigns (ab[(821)..(832 - 1)]), (ab[(832 + 821)..(832 * 2 - 1)]);
        loop variant 832 - 821 - i;
    */
    for (i = NTRU_N; i < L; i++) {
        ab[i] = 0;
        ab[L + i] = 0;
    }

    toom4_k2x2_mul(ab, ab, ab + L);

    /*@
        loop invariant 0 <= i <= 821;
        loop assigns (r->coeffs[0..(821 - 1)]);
        loop variant 821 - i;
    */
    for (i = 0; i < NTRU_N; i++) {
        r->coeffs[i] = ab[i] + ab[NTRU_N + i];
    }
}

/*@
    requires \initialized(a + (0..(832 - 1)));
    requires \initialized(b + (0..(832 - 1)));
    assigns ab[0..(2 * 832 - 1)];
*/
static void toom4_k2x2_mul(uint16_t ab[2 * L], const uint16_t a[L], const uint16_t b[L]) {
    uint16_t tmpA[9 * K];
    uint16_t tmpB[9 * K];
    uint16_t eC[63 * 2 * K];

    toom4_k2x2_eval_0(tmpA, a);
    toom4_k2x2_eval_0(tmpB, b);
    toom4_k2x2_basemul(eC + 0 * 9 * 2 * K, tmpA, tmpB);

    toom4_k2x2_eval_p1(tmpA, a);
    toom4_k2x2_eval_p1(tmpB, b);
    toom4_k2x2_basemul(eC + 1 * 9 * 2 * K, tmpA, tmpB);

    toom4_k2x2_eval_m1(tmpA, a);
    toom4_k2x2_eval_m1(tmpB, b);
    toom4_k2x2_basemul(eC + 2 * 9 * 2 * K, tmpA, tmpB);

    toom4_k2x2_eval_p2(tmpA, a);
    toom4_k2x2_eval_p2(tmpB, b);
    toom4_k2x2_basemul(eC + 3 * 9 * 2 * K, tmpA, tmpB);

    toom4_k2x2_eval_m2(tmpA, a);
    toom4_k2x2_eval_m2(tmpB, b);
    toom4_k2x2_basemul(eC + 4 * 9 * 2 * K, tmpA, tmpB);

    toom4_k2x2_eval_p3(tmpA, a);
    toom4_k2x2_eval_p3(tmpB, b);
    toom4_k2x2_basemul(eC + 5 * 9 * 2 * K, tmpA, tmpB);

    toom4_k2x2_eval_inf(tmpA, a);
    toom4_k2x2_eval_inf(tmpB, b);
    toom4_k2x2_basemul(eC + 6 * 9 * 2 * K, tmpA, tmpB);

    toom4_k2x2_interpolate(ab, eC);
}


/*@
    predicate k2x2_evaluated(uint16_t *r, integer until) =
        \forall integer i; (\valid(r + (0..until)) && 0 <= i < until) ==> (
            (r[4 * 52 + i] == r[i] + r[52 + i]) &&
            (r[5 * 52 + i] == r[52 + i] + r[3 * 52 + i]) &&
            (r[6 * 52 + i] == r[i] + r[2 * 52 + i]) &&
            (r[7 * 52 + i] == r[2 * 52 + i] + r[3 * 52 + i]) &&
            (r[8 * 52 + i] == r[i] + r[52 + i] + r[2 * 52 + i] + r[3 * 52 + i])
        );
*/

/*@
    requires \initialized(a + (0..(208 - 1)));
    assigns r[0..(9 * 52 - 1)];
    ensures \forall integer j; 0 <= j < 208 ==> \at(r[j], Post) == a[j];
    ensures k2x2_evaluated(\at(r, Post), 52);
*/
static void toom4_k2x2_eval_0(uint16_t r[9 * K], const uint16_t a[M]) {
    /*@
        loop invariant 0 <= i <= 208;
        loop invariant \forall integer j; 0 <= j < i ==> r[j] == a[j];
        loop assigns r[0..(208 - 1)];
        loop variant (208 - i);
    */
    for (size_t i = 0; i < M; i++) {
        r[i] = a[i];
    }
    k2x2_eval(r);
}

/* This function is INCORRECT: Unsafe use of memory */
/*@
    requires \initialized(a + (0..(208 * 4 - 1)));
    assigns r[0..(9 * 52 - 1)];
    ensures \forall integer j; 0 <= j < 208 ==> \at(r[j], Post) == (a[j] + a[208 + j] + a[2 * 208 + j] + a[3 * 208 + j]);
    ensures k2x2_evaluated(\at(r, Post), 52);
*/
static void toom4_k2x2_eval_p1(uint16_t r[9 * K], const uint16_t a[M]) {
    /*@
        loop invariant 0 <= i <= 208;
        loop invariant \forall integer j; 0 <= j < i ==> r[j] == (a[j] + a[208 + j] + a[2 * 208 + j] + a[3 * 208 + j]);
        loop assigns r[0..(208 - 1)];
        loop variant (208 - i);
    */
    for (size_t i = 0; i < M; i++) {
        r[i]  = a[0 * M + i];
        r[i] += a[1 * M + i];
        r[i] += a[2 * M + i];
        r[i] += a[3 * M + i];
    }
    k2x2_eval(r);
}

/* This function is INCORRECT: Unsafe use of memory */
/*@
    requires \initialized(a + (0..(208 * 4 - 1)));
    assigns r[0..(9 * 52 - 1)];
    ensures \forall integer j; 0 <= j < 208 ==> \at(r[j], Post) == (a[j] + a[208 + j] + a[2 * 208 + j] + a[3 * 208 + j]);
    ensures k2x2_evaluated(\at(r, Post), 52);
*/
static void toom4_k2x2_eval_m1(uint16_t r[9 * K], const uint16_t a[M]) {
    /*@
        loop invariant 0 <= i <= 208;
        loop invariant \forall integer j; 0 <= j < i ==> r[j] == (a[j] + a[208 + j] + a[2 * 208 + j] + a[3 * 208 + j]);
        loop assigns r[0..(208 - 1)];
        loop variant (208 - i);
    */
    for (size_t i = 0; i < M; i++) {
        r[i]  = a[0 * M + i];
        r[i] -= a[1 * M + i];
        r[i] += a[2 * M + i];
        r[i] -= a[3 * M + i];
    }
    k2x2_eval(r);
}

/* This function is INCORRECT: Unsafe use of memory */
/*@
    requires \initialized(a + (0..(208 * 4 - 1)));
    assigns r[0..(9 * 52 - 1)];
    ensures \forall integer j; 0 <= j < 208 ==> \at(r[j], Post) == (a[j] + 2 * a[208 + j] + 4 * a[2 * 208 + j] + 8 * a[3 * 208 + j]);
    ensures k2x2_evaluated(\at(r, Post), 52);
*/
static void toom4_k2x2_eval_p2(uint16_t r[9 * K], const uint16_t a[M]) {
    /*@
        loop invariant 0 <= i <= 208;
        loop invariant \forall integer j; 0 <= j < i ==> r[j] == (a[j] + 2 * a[208 + j] + 4 * a[2 * 208 + j] + 8 * a[3 * 208 + j]);
        loop assigns r[0..(208 - 1)];
        loop variant (208 - i);
    */
    for (size_t i = 0; i < M; i++) {
        r[i]  = a[0 * M + i];
        r[i] += 2 * a[1 * M + i];
        r[i] += 4 * a[2 * M + i];
        r[i] += 8 * a[3 * M + i];
    }
    k2x2_eval(r);
}

/* This function is INCORRECT: Unsafe use of memory */
/*@
    requires \initialized(a + (0..(208 * 4 - 1)));
    assigns r[0..(9 * 52 - 1)];
    ensures \forall integer j; 0 <= j < 208 ==> \at(r[j], Post) == (a[j] + 2 * a[208 + j] + 4 * a[2 * 208 + j] + 8 * a[3 * 208 + j]);
    ensures k2x2_evaluated(\at(r, Post), 52);
*/
static void toom4_k2x2_eval_m2(uint16_t r[9 * K], const uint16_t a[M]) {
    /*@
        loop invariant 0 <= i <= 208;
        loop invariant \forall integer j; 0 <= j < i ==> r[j] == (a[j] + 2 * a[208 + j] + 4 * a[2 * 208 + j] + 8 * a[3 * 208 + j]);
        loop assigns r[0..(208 - 1)];
        loop variant (208 - i);
    */
    for (size_t i = 0; i < M; i++) {
        r[i]  = a[0 * M + i];
        r[i] -= 2 * a[1 * M + i];
        r[i] += 4 * a[2 * M + i];
        r[i] -= 8 * a[3 * M + i];
    }
    k2x2_eval(r);
}

/* This function is INCORRECT: Unsafe use of memory */
/*@
    requires \initialized(a + (0..(208 * 4 - 1)));
    assigns r[0..(9 * 52 - 1)];
    ensures \forall integer j; 0 <= j < 208 ==> \at(r[j], Post) == (a[j] + 3 * a[208 + j] + 9 * a[2 * 208 + j] + 27 * a[3 * 208 + j]);
    ensures k2x2_evaluated(\at(r, Post), 52);
*/
static void toom4_k2x2_eval_p3(uint16_t r[9 * K], const uint16_t a[M]) {
    /*@
        loop invariant 0 <= i <= 208;
        loop invariant \forall integer j; 0 <= j < i ==> r[j] == (a[j] + 3 * a[208 + j] + 9 * a[2 * 208 + j] + 27 * a[3 * 208 + j]);
        loop assigns r[0..(208 - 1)];
        loop variant (208 - i);
    */
    for (size_t i = 0; i < M; i++) {
        r[i]  = a[0 * M + i];
        r[i] += 3 * a[1 * M + i];
        r[i] += 9 * a[2 * M + i];
        r[i] += 27 * a[3 * M + i];
    }
    k2x2_eval(r);
}

/* This function is INCORRECT: Unsafe use of memory */
/*@
    requires \initialized(a + (0..(208 * 4 - 1)));
    assigns r[0..(9 * 52 - 1)];
    ensures \forall integer j; 0 <= j < 208 ==> \at(r[j], Post) == a[3 * 208 + j];
    ensures k2x2_evaluated(\at(r, Post), 52);
*/
static void toom4_k2x2_eval_inf(uint16_t r[9 * K], const uint16_t a[M]) {
    /*@
        loop invariant 0 <= i <= 208;
        loop invariant \forall integer j; 0 <= j < i ==> r[j] == a[3 * 208 + j];
        loop assigns r[0..(208 - 1)];
        loop variant (208 - i);
    */
    for (size_t i = 0; i < M; i++) {
        r[i] = a[3 * M + i];
    }
    k2x2_eval(r);
}

/*@
    requires \initialized (r + (0..(4 * 52 - 1)));
    assigns r[(4 * 52)..(9 * 52 - 1)];
    ensures k2x2_evaluated(r, 52);
*/
static inline void k2x2_eval(uint16_t r[9 * K]) {
    /* Input:  e + f.Y + g.Y^2 + h.Y^3                              */
    /* Output: [ e | f | g | h | e+f | f+h | g+e | h+g | e+f+g+h ]  */

    size_t i;
    /*@
        loop invariant 0 <= i <= 4 * 52;
        loop invariant \forall integer j; 0 <= j < i ==> r[j] == r[4 * 52 + j];
        loop assigns i;
        loop assigns r[(4 * 52)..(2 * 4 * 52 - 1)];
        loop variant (4 * 52 - i);
    */
    for (i = 0; i < 4 * K; i++) {
        r[4 * K + i] = r[i];
    }

    /*@
        loop invariant 0 <= i <= 52;
        loop invariant k2x2_evaluated(r, i);
        loop assigns i;
        loop assigns r[(4 * 52)..(9 * 52 - 1)];
        loop variant (52 - i);
    */
    for (i = 0; i < K; i++) {
        r[4 * K + i] += r[1 * K + i];
        r[5 * K + i] += r[3 * K + i];
        r[6 * K + i] += r[0 * K + i];
        r[7 * K + i] += r[2 * K + i];
        r[8 * K + i] = r[5 * K + i];
        r[8 * K + i] += r[6 * K + i];
    }
}

/*@
    requires \initialized(a + (0..(9 * 52 - 1)));
    requires \initialized(b + (0..(9 * 52 - 1)));
    requires \valid(r + (0..(16 * 52 + 2 * 52 - 1)));
    assigns r[0..(16 * 52 + 2 * 52 - 1)];
*/
static void toom4_k2x2_basemul(uint16_t r[18 * K], const uint16_t a[9 * K], const uint16_t b[9 * K]) {
    schoolbook_KxK(r + 0 * 2 * K, a + 0 * K, b + 0 * K);
    schoolbook_KxK(r + 1 * 2 * K, a + 1 * K, b + 1 * K);
    schoolbook_KxK(r + 2 * 2 * K, a + 2 * K, b + 2 * K);
    schoolbook_KxK(r + 3 * 2 * K, a + 3 * K, b + 3 * K);
    schoolbook_KxK(r + 4 * 2 * K, a + 4 * K, b + 4 * K);
    schoolbook_KxK(r + 5 * 2 * K, a + 5 * K, b + 5 * K);
    schoolbook_KxK(r + 6 * 2 * K, a + 6 * K, b + 6 * K);
    schoolbook_KxK(r + 7 * 2 * K, a + 7 * K, b + 7 * K);
    schoolbook_KxK(r + 8 * 2 * K, a + 8 * K, b + 8 * K);
}

/*@
    requires \initialized(a + (0..(52 - 1)));
    requires \initialized(b + (0..(52 - 1)));
    assigns r[0..(2 * 52 - 1)];
*/
static inline void schoolbook_KxK(uint16_t r[2 * K], const uint16_t a[K], const uint16_t b[K]) {
    size_t i, j;
    /*@
        loop invariant 0 <= j <= 52;
        loop assigns j, r[0..(52 - 1)];
        loop variant 52 - j;
    */
    for (j = 0; j < K; j++) {
        r[j] = a[0] * (uint32_t)b[j];
    }
    /*@
        loop invariant 1 <= i <= 52;
        loop assigns i, j, r[0..(2 * 52 - 2)];
        loop variant 52 - i;
    */
    for (i = 1; i < K; i++) {
        /*@
            loop invariant 0 <= j <= 52 - 1;
            loop assigns j, r[0..(2 * 52 - 2)];
            loop variant 52 - 1 - j;
        */
        for (j = 0; j < K - 1; j++) {
            r[i + j] += a[i] * (uint32_t)b[j];
        }
        r[i + K - 1] = a[i] * (uint32_t)b[K - 1];
    }
    r[2 * K - 1] = 0;
}

/* This function is INCORRECT: Unsafe use of memory */
/*@
    requires \valid_read(a + (0..(7 * 18 * 52 - 1)));
    requires \initialized(a + (0..(7 * 18 * 52 - 1)));
    requires \valid(r + (0..(6 * 208 + 8 * 52 - 1)));
    assigns r[0..(6 * 208 + 8 * 52 - 1)];
*/
static void toom4_k2x2_interpolate(uint16_t r[2 * M], const uint16_t a[7 * 18 * K]) {
    size_t i;

    uint16_t P1[2 * M];
    uint16_t Pm1[2 * M];
    uint16_t P2[2 * M];
    uint16_t Pm2[2 * M];

    uint16_t *C0 = r;
    uint16_t *C2 = r + 2 * M;
    uint16_t *C4 = r + 4 * M;
    uint16_t *C6 = r + 6 * M;

    uint16_t V0, V1, V2;

    k2x2_interpolate(C0, a + 0 * 9 * 2 * K);
    k2x2_interpolate(P1, a + 1 * 9 * 2 * K);
    k2x2_interpolate(Pm1, a + 2 * 9 * 2 * K);
    k2x2_interpolate(P2, a + 3 * 9 * 2 * K);
    k2x2_interpolate(Pm2, a + 4 * 9 * 2 * K);
    k2x2_interpolate(C6, a + 6 * 9 * 2 * K);

    /*@
        loop invariant 0 <= i <= 2 * 208;
        loop assigns i, V0, V1, (P1[0..(2 * 208 - 1)]), (r[(2 * 208)..(6 * 208 - 1)]);
        loop variant 2 * 208 - i;
    */
    for (i = 0; i < 2 * M; i++) {
        V0 = ((uint32_t)(P1[i] + Pm1[i])) >> 1;
        V0 = V0 - C0[i] - C6[i];
        V1 = ((uint32_t)(P2[i] + Pm2[i] - 2 * C0[i] - 128 * C6[i])) >> 3;
        C4[i] = 43691 * (uint32_t)(V1 - V0);
        C2[i] = V0 - C4[i];
        P1[i] = ((uint32_t)(P1[i] - Pm1[i])) >> 1;
    }

    /* reuse Pm1 for P3 */
#define P3 Pm1
    k2x2_interpolate(P3, a + 5 * 9 * 2 * K);

    /*@
        loop invariant 0 <= i <= 2 * 208;
        loop assigns i, V0, V1, V2, (P1[0..(2 * 208 - 1)]), (P2[0..(2 * 208 - 1)]), (Pm1[0..(2 * 208 - 1)]);
        loop variant 2 * 208 - i;
    */
    for (i = 0; i < 2 * M; i++) {
        V0 = P1[i];
        V1 = 43691 * (((uint32_t)(P2[i] - Pm2[i]) >> 2) - V0);
        V2 = 43691 * (uint32_t)(P3[i] - C0[i] - 9 * (C2[i] + 9 * (C4[i] + 9 * C6[i])));
        V2 = ((uint32_t)(V2 - V0)) >> 3;
        V2 -= V1;
        P3[i] = 52429 * (uint32_t)V2;
        P2[i] = V1 - V2;
        P1[i] = V0 - P2[i] - P3[i];
    }

    /*@
        loop invariant 0 <= i <= 2 * 208;
        loop assigns i, (r[(1 * 208)..(7 * 208 - 1)]);
        loop variant 2 * 208 - i;
    */
    for (i = 0; i < 2 * M; i++) {
        r[1 * M + i] += P1[i];
        r[3 * M + i] += P2[i];
        r[5 * M + i] += P3[i];
    }
}

/* This function is INCORRECT: Unsafe use of memory */
/*@
    requires \valid_read(a + (0..(16 * 52 + 2 * 52 - 1)));
    requires \initialized(a + (0..(16 * 52 + 2 * 52 - 1)));
    requires \valid(r + (0..(8 * 52 - 1)));
    assigns r[0..(8 * 52 - 1)];
*/
static inline void k2x2_interpolate(uint16_t r[M], const uint16_t a[9 * K]) {
    size_t i;
    uint16_t tmp[4 * K];

    /*@
        loop invariant 0 <= i <= 2 * 52;
        loop assigns i, r[0..(4 * 52 - 1)];
        loop variant 2 * 52 - i;
    */
    for (i = 0; i < 2 * K; i++) {
        r[0 * K + i] = a[0 * K + i];
        r[2 * K + i] = a[2 * K + i];
    }

    /*@
        loop invariant 0 <= i <= 2 * 52;
        loop assigns i, r[(1 * 52)..(3 * 52 - 1)];
        loop variant 2 * 52 - i;
    */
    for (i = 0; i < 2 * K; i++) {
        r[1 * K + i] += a[8 * K + i] - a[0 * K + i] - a[2 * K + i];
    }

    /*@
        loop invariant 0 <= i <= 2 * 52;
        loop assigns i, r[(4 * 52)..(8 * 52 - 1)];
        loop variant 2 * 52 - i;
    */
    for (i = 0; i < 2 * K; i++) {
        r[4 * K + i] = a[4 * K + i];
        r[6 * K + i] = a[6 * K + i];
    }

    /*@
        loop invariant 0 <= i <= 2 * 52;
        loop assigns i, r[(5 * 52)..(7 * 52 - 1)];
        loop variant 2 * 52 - i;
    */
    for (i = 0; i < 2 * K; i++) {
        r[5 * K + i] += a[14 * K + i] - a[4 * K + i] - a[6 * K + i];
    }

    /*@
        loop invariant 0 <= i <= 2 * 52;
        loop assigns i, tmp[0..(4 * 52 - 1)];
        loop variant 2 * 52 - i;
    */
    for (i = 0; i < 2 * K; i++) {
        tmp[0 * K + i] = a[12 * K + i];
        tmp[2 * K + i] = a[10 * K + i];
    }

    /*@
        loop invariant 0 <= i <= 2 * 52;
        loop assigns i, tmp[(1 * 52)..(3 * 52 - 1)];
        loop variant 2 * 52 - i;
    */
    for (i = 0; i < 2 * K; i++) {
        tmp[K + i] += a[16 * K + i] - a[12 * K + i] - a[10 * K + i];
    }

    /*@
        loop invariant 0 <= i <= 2 * 52;
        loop assigns i, tmp[0..(2 * 52 - 1)];
        loop variant 2 * 52 - i;
    */
    for (i = 0; i < 4 * K; i++) {
        tmp[0 * K + i] = tmp[0 * K + i] - r[0 * K + i] - r[4 * K + i];
    }

    /*@
        loop invariant 0 <= i <= 2 * 52;
        loop assigns i, r[(2 * 52)..(4 * 52 - 1)];
        loop variant 2 * 52 - i;
    */
    for (i = 0; i < 4 * K; i++) {
        r[2 * K + i] += tmp[0 * K + i];
    }
}

