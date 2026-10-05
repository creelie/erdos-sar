/*
 * Empirical distribution of rho'(z) = prod_{p | z, p >= 5} (1 - 1/p).
 *
 * For every threshold theta in a fixed list, count the odd z <= N and the
 * units z <= N (z = 1, 5 mod 6) with rho'(z) < theta, and print the counts
 * divided by the number of odd numbers and of units in [1, N].  These are the
 * proportions that the certified bounds beta(theta) of the paper dominate.
 *
 * Build:  cc -O2 -o rho_density rho_density.c -lm
 * Run:    ./rho_density 100000000 > data/rho_density.csv
 */
#include <stdio.h>
#include <stdlib.h>

#define NTH 121                 /* thresholds 0.40, 0.405, ..., 1.00 */

int main(int argc, char **argv)
{
    long n = argc > 1 ? atol(argv[1]) : 100000000L;
    double *rho = malloc((n + 1) * sizeof *rho);
    char *composite = calloc(n + 1, 1);
    if (!rho || !composite) { fprintf(stderr, "out of memory\n"); return 1; }
    for (long z = 0; z <= n; z++) rho[z] = 1.0;

    /* sieve of Eratosthenes; each prime p >= 5 multiplies rho on its multiples */
    for (long p = 2; p <= n; p++) {
        if (composite[p]) continue;
        if (p * p <= n)
            for (long m = p * p; m <= n; m += p) composite[m] = 1;
        if (p >= 5) {
            double f = 1.0 - 1.0 / (double)p;
            for (long m = p; m <= n; m += p) rho[m] *= f;
        }
    }
    free(composite);

    double theta[NTH];
    for (int j = 0; j < NTH; j++) theta[j] = 0.40 + 0.005 * j;
    long hodd[NTH + 1] = {0}, hunit[NTH + 1] = {0}, nodd = 0, nunit = 0;

    for (long z = 1; z <= n; z++) {
        if (z % 2 == 0) continue;
        /* first threshold strictly above rho'(z); the margin guards exact ties */
        int lo = 0, hi = NTH;
        while (lo < hi) {
            int mid = (lo + hi) / 2;
            if (theta[mid] > rho[z] + 1e-12) hi = mid; else lo = mid + 1;
        }
        hodd[lo]++; nodd++;
        if (z % 3 != 0) { hunit[lo]++; nunit++; }
    }
    free(rho);

    printf("theta,odd,unit\n");
    long codd = 0, cunit = 0;
    for (int j = 0; j < NTH; j++) {
        codd += hodd[j]; cunit += hunit[j];
        printf("%.3f,%.6f,%.6f\n", theta[j], (double)codd / nodd, (double)cunit / nunit);
    }
    return 0;
}
