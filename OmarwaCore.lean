/-
  OMARWA Core — Aggregate Imports (v25)
  ======================================
  Ar-Ge Alanı: Temel Bilimler / Sayı Teorisi
  TRL Seviyesi: 5 (Gate-A → Gate-B)
  Protokol ID: OTT-LEAN-CORE

  Bu dosya, OMARWA çekirdek Lean modüllerini tek noktadan içeri alır.
  İçerik:
    ── Temel Katman ──
    - OmarwaCore.Sequence             (Tₖ tanımı ve temel özellikler)
    - OmarwaCore.ModularPeriods       (mod 9/11/27 ve super-period)
    - OmarwaCore.MersenneFermat       (T8/T9 periodik kanunlar, genel-n)
    ── Yapısal Katman ──
    - OmarwaCore.FractalLaws          (Fraktal periyot yasaları)
    - OmarwaCore.CoxeterNumber        (E₈ Coxeter sayısı h=30)
    - OmarwaCore.SuperPeriod          (Süper-periyot türetimi)
    - OmarwaCore.WeylExponents        (E₈ Weyl üstelleri)
    ── v15 Keşifler ──
    - OmarwaCore.ProductTheorem       (P(77)=30, alternatif Coxeter)
    - OmarwaCore.DeepArithmetic       (φ(1453), P(1711), primitif kökler)
    - OmarwaCore.CollatzFibonacci     (Collatz köprüsü, ord₅₇₇(2)=F₁₂)
    - OmarwaCore.SabbathNode          (T₆=385 üçlü sıfırlama, primalite)
    - OmarwaCore.PalindromicInvolution(354≡453, antipodal, P(360), CRT)
    - OmarwaCore.ResidueDR            (Dijital kök biseksiyonu, triseksiyon)
    ── v16 Manifold / Topoloji ──
    - OmarwaCore.HopfFibration        (Σ³→S² Hopf, 29-1-29, 370 holoarşi)
    ── v16 MTY Ağ Teoremleri ──
    - OmarwaCore.NetworkTheorems      (MT-1…MT-14 + Ana Teorem, 354/177/59 ağ kimliği)
    ── v17 Affine Operator & CRT ──
    - OmarwaCore.AffineOperator       (6n+1 iskelet, Örnekleme Teoremi, Core Reduction)
    - OmarwaCore.CenteredHexagonal    (Merkezli altıgen sayılar, H_n ≡ 1 mod 6)
    - OmarwaCore.CRTIntertwining      (CRT kaldırma ι, 354 anatomisi, periyot köprüsü)
    ── v18 Fiziksel Yapılar (Part 3-4 Gate-A) ──
    - OmarwaCore.ChernSimonsLevel     (k_CS=30, Berry γ=15π, C₁=15, anyon istatistiği)
    - OmarwaCore.TopologicalWinding   (T³ sarım (15,3,5), çarpım=225, toplam=23)
    - OmarwaCore.PhysicalScaling      (Koppa q̃=d/d_c, APEX tetikleme, α_k→1/2)
    ── v19 Exceptional Universality ──
    - OmarwaCore.ExceptionalUniversality (G2/F4/E6/E7/E8 Coxeter = OMARWA)
    ── v20 Holon & Crystallographic Locks ──
    - OmarwaCore.HolonCrystallographic   (Trinity 407=11×37, Double Lock, Pisano sync, 4 perfect points)
    ── v21 Pascal–Sierpiński–Fibonacci ──
    - OmarwaCore.PascalSierpinski        (Kummer, Sierpiński levels, Fibonacci diagonal, Pisano sync table)
    ── v22 Composite Modular Periods ──
    - OmarwaCore.CompositeModular        (P(33)=10, P(99)=10, P(407)=180, P(777)=36, P(999)=36, P(1453)=1452, period families)
    ── v23 Forbidden Unity & Ribbon ──
    - OmarwaCore.ForbiddenUnityRibbon    (Forbidden Unity, Residue Sum, P(121)=110, Dual Shield, CRT, orbit)
    ── v24 Fractal Holon & Palindromic Time Code ──
    - OmarwaCore.FractalHolon            (FS-1..FS-9: 111 mod 11=1, P(111/333/729), ord₁₁(4)=5, 354.1.1.1.453, Weyl bipyramid)
    ── v25 Grand Synthesis: Pascal–Sierpiński–Fibonacci–Helical ──
    - OmarwaCore.GrandSynthesis          (GS-1..GS-10: Fibonacci residues in mod 11, α-Unity Axis, CRT Pascal, Thue-Morse, Lucas L₅=11, DNA, wing sums)-/

-- ── Temel Katman ──
import OmarwaCore.Sequence
import OmarwaCore.ModularPeriods
import OmarwaCore.MersenneFermat
-- ── Yapısal Katman ──
import OmarwaCore.FractalLaws
import OmarwaCore.CoxeterNumber
import OmarwaCore.SuperPeriod
import OmarwaCore.WeylExponents
-- ── v15 Keşifler ──
import OmarwaCore.ProductTheorem
import OmarwaCore.DeepArithmetic
import OmarwaCore.CollatzFibonacci
import OmarwaCore.SabbathNode
import OmarwaCore.PalindromicInvolution
import OmarwaCore.ResidueDR
-- ── v16 Manifold / Topoloji ──
import OmarwaCore.HopfFibration
-- ── v16 MTY Ağ Teoremleri ──
import OmarwaCore.NetworkTheorems
-- ── v17 Affine Operator & CRT ──
import OmarwaCore.AffineOperator
import OmarwaCore.CenteredHexagonal
import OmarwaCore.CRTIntertwining
-- ── v19 Exceptional Universality ──
import OmarwaCore.ExceptionalUniversality
-- ── v20 Holon & Crystallographic Locks ──
import OmarwaCore.HolonCrystallographic
-- ── v21 Pascal–Sierpiński–Fibonacci ──
import OmarwaCore.PascalSierpinski
-- ── v18 Fiziksel Yapılar (Part 3-4 Gate-A) ──
import OmarwaCore.ChernSimonsLevel
import OmarwaCore.TopologicalWinding
import OmarwaCore.PhysicalScaling
-- ── v22 Composite Modular Periods ──
import OmarwaCore.CompositeModular
-- ── v23 Forbidden Unity & Ribbon ──
import OmarwaCore.ForbiddenUnityRibbon
-- ── v24 Fractal Holon & Palindromic Time Code ──
import OmarwaCore.FractalHolon
-- ── v25 Grand Synthesis: Pascal–Sierpiński–Fibonacci–Helical ──
import OmarwaCore.GrandSynthesis
