# OmarwaCore

**Lean 4 Formalization of the OMARWA Sequence $T_k = 6 \cdot 2^k + 1$ (OEIS [A004119](https://oeis.org/A004119))**

| Metric | Value |
|--------|-------|
| Lean 4 | v4.29.0-rc3 |
| Mathlib | master |
| Modules | 28 |
| Theorems + Lemmas | 956 |
| Lines of Proof | 5,779 |
| `sorry` axioms | **0** |

## Overview

OmarwaCore is a complete Lean 4 formalization of the mathematical properties of the integer sequence

$$T_k = 6 \cdot 2^k + 1 \quad (k \geq 0): \quad 7, 13, 25, 49, 97, 193, 385, 769, 1537, \ldots$$

All principal results are machine-verified with zero `sorry` axioms, building on Mathlib4.

## Key Results

| Module | Content | Theorems |
|--------|---------|:--------:|
| `Sequence` | $T_k$ definition, basic properties, induction | Core |
| `ModularPeriods` | $P(m) = \operatorname{ord}_{m'}(2)$ where $m' = m / \gcd(m,6)$ | Core Reduction |
| `FractalLaws` | $P(p^n) = d_0 \cdot p^{n-1}$ for non-Wieferich primes | Fractal Laws |
| `SuperPeriod` | $L = \operatorname{lcm}(P(9), P(11)) = 30$ (three derivations) | Super-Period |
| `ProductTheorem` | $P(m_1 m_2) = \operatorname{lcm}(P(m_1), P(m_2))$ via CRT | Product Theorem |
| `MersenneFermat` | Mersenne/Fermat special cases | Special Values |
| `AffineOperator` | $6n+1$ affine skeleton, Core Reduction | Operator Structure |
| `CenteredHexagonal` | $H_n \equiv 1 \pmod{6}$, centered hexagonal intersections | Hexagonal |
| `CRTIntertwining` | CRT lifting $\iota$, period bridge, 354 anatomy | CRT |
| `CoxeterNumber` | $h(E_8) = 30 = L$ correspondence | Coxeter |
| `WeylExponents` | $E_8$ Weyl exponents alignment | Weyl |
| `PalindromicInvolution` | 354 ≡ 453, antipodal involution, $P(360)$ | Palindromic |
| `ResidueDR` | Digital root bisection/trisection | Residue |
| `DeepArithmetic` | $\varphi(1453)$, $P(1711)$, primitive roots | Deep Arithmetic |
| `CollatzFibonacci` | Collatz bridge, $\operatorname{ord}_{577}(2) = F_{12}$ | Collatz–Fibonacci |
| `SabbathNode` | $T_6 = 385$ triple zero, primality | Sabbath |
| `HopfFibration` | $\Sigma^3 \to S^2$ Hopf, 29-1-29, 370 holarchy | Hopf |
| `NetworkTheorems` | MT-1…MT-14 + Main Theorem, 354/177/59 identity | Network |
| `ChernSimonsLevel` | $k_{CS} = 30$, Berry phase, $C_1 = 15$ | Chern–Simons |
| `TopologicalWinding` | $T^3$ winding $(15,3,5)$, product = 225 | Topological |
| `PhysicalScaling` | Koppa $\tilde{q} = d/d_c$, APEX triggering | Physical Scaling |
| `ExceptionalUniversality` | G₂/F₄/E₆/E₇/E₈ Coxeter = OMARWA | Exceptional |
| `HolonCrystallographic` | Trinity 407 = 11×37, Double Lock, Pisano sync | Holon |
| `PascalSierpinski` | Kummer, Sierpiński levels, Fibonacci diagonal | Pascal–Sierpiński |
| `CompositeModular` | $P(33), P(99), P(407), P(777), P(999), P(1453)$ | Composite |
| `ForbiddenUnityRibbon` | Forbidden Unity, $P(121) = 110$, Dual Shield | Forbidden Unity |
| `FractalHolon` | 111 mod 11 = 1, $P(111/333/729)$, Weyl bipyramid | Fractal Holon |
| `GrandSynthesis` | GS-1…GS-10: Five-way bridge theorem | Grand Synthesis |

## Building

### Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean version manager)
- Internet connection (for Mathlib download on first build)

### Build

```bash
# Clone
git clone https://github.com/omarwa622/OmarwaCore.git
cd OmarwaCore

# Build (first build downloads Mathlib — may take several minutes)
lake build
```

A successful build with zero errors confirms that all 956 theorems are formally verified.

### Verify Statistics

```bash
# Count theorems + lemmas
grep -r "theorem \|lemma " OmarwaCore/ --include="*.lean" | wc -l

# Count lines of proof code
find OmarwaCore/ -name "*.lean" -exec cat {} + | wc -l

# Check for sorry
grep -r "sorry" OmarwaCore/ --include="*.lean" | grep -v "^--" | wc -l
```

## Module Dependency

```
OmarwaCore.lean  (root — imports all 28 modules)
├── Sequence           ← core definition
├── ModularPeriods     ← depends on Sequence
├── MersenneFermat     ← depends on Sequence
├── FractalLaws        ← depends on ModularPeriods
├── SuperPeriod        ← depends on ModularPeriods
├── ProductTheorem     ← depends on ModularPeriods
├── CoxeterNumber      ← depends on SuperPeriod
├── WeylExponents      ← depends on CoxeterNumber
├── AffineOperator     ← depends on Sequence
├── CenteredHexagonal  ← standalone
├── CRTIntertwining    ← depends on ProductTheorem
├── ...                   (remaining modules extend the above)
└── GrandSynthesis     ← depends on PascalSierpinski, FractalHolon
```

## Mathematical Content Summary

The formalization establishes a complete theory of modular periodicity for $T_k = 6 \cdot 2^k + 1$:

1. **Core Reduction Theorem:** $P(m) = \operatorname{ord}_{m'}(2)$ where $m' = m / \gcd(m, 6)$
2. **Fractal Period Laws:** $P(p^n) = d_0 \cdot p^{n-1}$ for primes $p \nmid 6$ (non-Wieferich)
3. **Product Theorem (CRT):** $P(m_1 m_2) = \operatorname{lcm}(P(m_1), P(m_2))$ for $\gcd(m_1, m_2) = 1$
4. **Super-Period:** $L = \operatorname{lcm}(P(9), P(11)) = \operatorname{lcm}(2, 10) = 30$, derived independently via three paths
5. **GCD Law:** $\gcd(T_i, T_j) \mid 2^{|i-j|} - 1$
6. **Palindromic Involution:** 354 ≡ 453 mod period, antipodal symmetry
7. **Grand Synthesis:** Five-way bridge connecting Pascal triangle, Sierpiński fractal, Fibonacci sequence, helical orbits, and modular periodicity

## Relation to Published Work

This formalization accompanies the following publications:

- **Preprint:** *Modular Period Structure and Fractal Laws of the Affine Sequence $T_k = 6 \cdot 2^k + 1$*
- **Dataset:** *Computational Verification Data for the OMARWA Sequence*

## Author

**Ömer Çetintaş**
- ORCID: [0009-0003-2977-6048](https://orcid.org/0009-0003-2977-6048)
- GitHub: [@omarwa622](https://github.com/omarwa622)

## License

Apache License 2.0 — see [LICENSE](LICENSE).

## Citation

If you use this formalization in your research, please cite:

```bibtex
@software{cetintas2026omarwacore,
  author    = {Çetintaş, Ömer},
  title     = {{OmarwaCore: Lean 4 Formalization of the OMARWA Sequence
               T_k = 6·2^k + 1}},
  year      = {2026},
  url       = {https://github.com/omarwa622/OmarwaCore},
  note      = {28 modules, 956 theorems, 0 sorry, Lean 4 v4.29.0-rc3 + Mathlib4}
}
```
