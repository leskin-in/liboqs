// Based on supercop-20190110/crypto_sort/int32/x86

#include "crypto_sort_int32.h"

#include <stdint.h>
#define int32 int32_t

#define int32_MINMAX(a,b) \
    do { \
        int32_t ab = (b) ^ (a); \
        int32_t c = (int32_t)((int64_t)(b) - (int64_t)(a)); \
        c ^= ab & (c ^ (b)); \
        c >>= 31; \
        c &= ab; \
        (a) ^= c; \
        (b) ^= c; \
    } while(0)

/* assume 2 <= n <= 0x40000000 */
/*
    axiomatic Increasing
    {
        predicate
        Increasing{L}(value_type * a, integer m, integer n) =
            \forall integer i, j; m <= i < j < n ==> a[i] <= a[j];
        predicate
        Increasing{L}(value_type * a, integer n) =
            Increasing{L}(a, 0, n);
    }

    axiomatic MultisetReorder
    {
        predicate
        MultisetReorder{K,L}(value_type * a, integer m, integer n) =
            \forall value_type v;
        predicate
        Count{K}(a, m, n, v) == Count{L}(a, m, n, v);
        predicate
        MultisetReorder{K,L}(value_type * a, integer n) =
            MultisetReorder{K,L}(a, 0, n);

        lemma Unchanged_MultisetReorder{K,L}:
            \forall value_type *a, integer k, n;
            Unchanged{K,L}(a, k, n) ==> MultisetReorder{K,L}(a, k, n);
        lemma MultisetReorder_DisjointUnion{K,L}:
            \forall value_type *a, integer i, k, n;
            0 <= i <= k <= n ==>
            MultisetReorder{K,L}(a, i, k) ==>
            MultisetReorder{K,L}(a, k, n) ==>
            MultisetReorder{K,L}(a, i, n);
        lemma MultisetReorder_Symmetric{K,L}:
            \forall value_type *a, integer m, n;
            MultisetReorder{K,L}(a, m, n) ==>
            MultisetReorder{L,K}(a, m, n);
        lemma MultisetReorder_Transitive{K,L,M}:
            \forall value_type *a, integer m, n;
            MultisetReorder{K,L}(a, m, n) ==>
            MultisetReorder{L,M}(a, m, n) ==>
            MultisetReorder{K,M}(a, m, n);
    }

    requires 2 <= n <= 0x40000000;
    requires \valid(array + (0..(n - 1)));
    assigns array[0..(n-1)];
    ensures Increasing(array, n);
    ensures MultisetReorder(array, n);
*/
void PQCLEAN_NTRUHPS4096821_CLEAN_crypto_sort_int32(int32 *array, size_t n) {
    size_t top, p, q, r, i, j;
    int32 *x = array;

    top = 1;
    /*@
        loop invariant top <= n;
        loop assigns top;
    */
    while (top < n - top) {
        top += top;
    }
    //@ assert top > n / 2;

    /*@
        loop invariant top >= p >= 0;
        loop assigns i, p, j, q, r, x[0..(n - 1)];
    */
    for (p = top; p >= 1; p >>= 1) {
        i = 0;
        /*@
            loop assigns i, j, x[0..(n - 1)];
        */
        while (i + 2 * p <= n) {
            /*@
                loop assigns j, x[0..(n - 1)];
            */
            for (j = i; j < i + p; ++j) {
                int32_MINMAX(x[j], x[j + p]);
            }
            i += 2 * p;
        }
        /*@
            loop assigns j, x[0..(n - 1)];
        */
        for (j = i; j < n - p; ++j) {
            int32_MINMAX(x[j], x[j + p]);
        }

        i = 0;
        j = 0;
        /*@
            loop assigns q, r, i, j, x[0..(n - 1)];
        */
        for (q = top; q > p; q >>= 1) {
            if (j != i) {
                /*@
                    loop assigns q, r, i, j, x[0..(n - 1)];
                */
                for (;;) {
                    if (j == n - q) {
                        goto done;
                    }
                    int32 a = x[j + p];
                    /*@
                        loop assigns r, a;
                    */
                    for (r = q; r > p; r >>= 1) {
                        int32_MINMAX(a, x[j + r]);
                    }
                    x[j + p] = a;
                    ++j;
                    if (j == i + p) {
                        i += 2 * p;
                        break;
                    }
                }
            }
            /*@
                loop assigns i, j, r, x[0..(n - 1)];
            */
            while (i + p <= n - q) {
                /*@
                    loop assigns j, r;
                */
                for (j = i; j < i + p; ++j) {
                    int32 a = x[j + p];
                    /*@
                        loop assigns r, a;
                    */
                    for (r = q; r > p; r >>= 1) {
                        int32_MINMAX(a, x[j + r]);
                    }
                    x[j + p] = a;
                }
                i += 2 * p;
            }
            /* now i + p > n - q */
            j = i;
            /*@
                loop assigns j, r, x[0..(n - 1)];
            */
            while (j < n - q) {
                int32 a = x[j + p];
                /*@
                    loop assigns r, a;
                */
                for (r = q; r > p; r >>= 1) {
                    int32_MINMAX(a, x[j + r]);
                }
                x[j + p] = a;
                ++j;
            }

done:
            ;
        }
    }
}
