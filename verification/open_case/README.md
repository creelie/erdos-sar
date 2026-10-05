# Proof plan for the open case (70 d > n) of Erdős #883 Q1

Notation: E* (≡2,4), M6 (≡0), O (≡3), U (≡1,5) mod 6, all in [1,n].
d=|E*\A|, μ6=|M6\A|, μO=|O\A|, u=|A∩U|, μT=d+μ6+μO.  From |A|>T(n): u ≥ μT+1 and
|A_odd| ≥ o(n)+1+d+μ6.  δ=3d/n, a=μ6/n, λ=μT/n.
Good(t) = {z∈A odd : ρ'(z) ≥ t},  GoodU(t) = {z∈A∩U : ρ'(z) ≥ t}.
Certificates: #{z≤n : z%6∈R, ρ'(z)<t} ≤ (n/6)|R| β(t) for n ≥ N(t), R symmetric.
So |Good(t)| ≥ |A_odd| − (n/2)β(t), |GoodU(t)| ≥ u − (n/3)β(t).

## Certificates (Cert.lean)
P = primes 5..19 (signatures S ⊆ P), T' = primes in [23, y], Big = primes in (y, n], y = 10^10.
ρ'(z) = ρ'(S)·φ_{T'}(z)·φ_Big(z);  φ_Big(z) ≥ 1 − Σ_{p∈Big,p|z} 1/p.
Markov: #{z≤n : Σ_{p∈Big,p|z}1/p > η} ≤ n/(η(y−1)), η = 10^-4.
Rankin on Z_S = {z ≤ n : z%6∈R, sig_P(z)=S}:  #{z∈Z_S, D|z} = CntR(⌊n/(∏S·D)⌋, R, P\S),
#{z∈Z_S : φ_{T'}(z) ≤ t} ≤ t^m [ (n/6)|R| dens(S) ∏_{T'}(1+g_m/p) + |R| 2^{|P|} ∏_{T'}(1+g_m) ].
β(θ) = Σ_S dens(S) min_{m∈menu}((θ'/ρ'(S))^m F̂_m) + Markov share, θ' = θ + 2/10^4.

## Scheme T (λ ≥ 9/50)
Pool A\U (size T(n)−μT), k_T = (T(n)−μT+2)/2 ≥ l. Gadgets: l−1 unit singletons with ρ' ≥ θT,
pair [w,w'] coprime units, ρ'(w) ≥ r1 (top unit), ρ'(w') ≥ t2, r1·t2 ≥ θT.
Unit degree into pool ≥ (2n/3)ρ' − err − μT.  Length 2(l−1)+3.
Box [λ0,λ1]: θT ≥ 1/2+3λ1/4+ε; λ0 ≥ 1/6+β(θT)/3+ε; λ0 ≥ β(r1)/3+ε; λ0 ≥ β(t2)/3+(1−r1)/3+ε.

## Scheme GP (λ < 9/50, δ > 3/70)
Pool B = E*∩A minus e1; k = (|E*|−d+2)/2 + ⌊κn⌋; Q = 1 if l ≤ k else l−k; σ = l−1−Q.
G = [g1, e1, w_0, y_0, w_1, ..., y_{Q−2}, w_{Q−1}, g2]  (|G| = 2Q+2), singletons S (|S|=σ).
 1. (g2, w_{Q−1}) coprime pair in Good(s) by coprime_pair; w_{Q−1} the unit one.
 2. g1 ∈ Good(t1), t1·s ≥ θ (joint degree of the ends).
 3. w_0..w_{Q−2}: units in GoodU(θw).
 4. e1 ∈ E*∩A coprime to g1·w_0.
 5. y_i ∈ M6∩A coprime to w_i w_{i+1}, greedy.
 6. singletons from Good(θ).
Length 2σ + (2Q+2) + 1 = 2l+1.  l = 2: 5-cycle [g1,e1,w,g2,β].
Box [δ0,δ1]×[a0,a1]:
 θ ≥ 1/2+δ1/2+3κ+ε;  Q1 mode: κ ≥ δ1/6+ε (then Q = 1 always).
 (P) δ0/3+a0 ≥ β(s)/2+ε   (G1) 1/6+δ0/3+a0 ≥ β(t1)/2+ε   (H3) t1·s ≥ θ
 (E) t1·min(θw,s) ≥ δ1+ε  (Q1: t1·s ≥ δ1+ε)
 (W) δ0/6+a0+κ ≥ β(θw)/3+ε   (Y) θw·min(θw,s)/6 ≥ δ1/6−κ+a1+ε   [GP mode only]
 (S) δ0/3+a0 ≥ β(θ)/2+ε.
Boxes: plan/boxes.json (3 T boxes, 29 GP boxes, 16 thresholds).
