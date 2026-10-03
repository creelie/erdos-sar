# Case B exploration (NOT a proof)

Case B = A omits more than n/70 of the numbers = 2,4 (mod 6). These scripts test a proposed
two-system strategy (two applications of Jackson's theorem, one path inserted into the other):

- dens.py: empirical distribution of rho' on the classes 3 (mod 6) and +-1 (mod 6).
- rigdens.py / mkrig.py: rigorous upper bounds G(r) for the density of {rho' < r} in such a class
  (exact DP over primes <= 300 with rounding up, plus a moment bound for larger primes). Output: GR.npy.
- feas5.py (true densities) / feas5r.py (rigorous bounds): grid check that, for every deletion
  profile (eps, sigma, tau, alpha) and every cycle-length fraction lambda, some allocation of the
  vertex pools satisfies the Jackson degree conditions in the worst-case model. Result: no failing
  grid point in either version.

What is still missing for a proof: (1) existence of the odd-parity unit (a pair of ends with a
large common neighbourhood joined by a path with an even number of vertices) in adversarial
configurations; (2) turning the finite grid check into a statement for all parameter values;
(3) the O(1) and O(sqrt n) bookkeeping.
