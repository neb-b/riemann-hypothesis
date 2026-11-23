module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExponentInequalityNondegenerateMid
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0165

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankSizeHypothesisExplicitConstantSiegelMass
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg
theorem xiSizes_explicit : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), 1 ≤ Cl → Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v (Cnt.NT D u) (BridgeLemma.XiB D large₂ u C) := by
  intro hS C hC D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hCl hH
  have he : (1 : ℝ) ≤ Real.exp 1 * Real.pi := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    nlinarith
  have hmax : max 1 (1 / Cl) ≤ 1 := max_le le_rfl (by rw [div_le_one (by linarith)]; exact hCl)
  have hM2 := Formalism.MainNotions.BridgeLemma₂.plane_mass_bound_parameters D large₂ u u' C' Cl Cg cb Cu cT CT C0 A 8
    (le_trans (mul_le_mul_of_nonneg_left hmax (by norm_num)) (by norm_num))
  have hX := Formalism.MainNotions.BridgeLemma.first_bound_of_mass_ratio D large₂ u u' C' Cl Cg cb Cu cT CT C0 A 8 408
    (Formalism.MainNotions.BridgeLemma.lattice_count_first_of_siegel hS D) hM2 (by norm_num) le_rfl hCl
  have hCX : |(408 : ℝ)| * max 1 |Real.exp 1 * Real.pi| ≤ C := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 408), abs_of_pos (by positivity), max_eq_right he]; exact hC
  have hXi := Formalism.MainNotions.BridgeLemma.xiHyp_of_stX D large₂ hH hX hCX (by linarith)
  rw [← Formalism.MainNotions.BridgeLemma.d_m_eq D]
  exact hXi
end GlobalTheory.Core.Deg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankSumsBoundWithExpLoss
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem rpow_le_rpow_both {x y u w : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hu : 0 ≤ u) (huw : u ≤ w) :
    x ^ u ≤ y ^ w :=
  (Real.rpow_le_rpow_of_exponent_le hx huw).trans
    (Real.rpow_le_rpow (by linarith) hxy (hu.trans huw))

theorem bigH_one_le (C : ℝ) (hC : 0 ≤ C) (m f : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    1 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH
  exact Real.one_le_rpow hb (by positivity)

theorem bigH_mono {C D : ℝ} (hC : 0 ≤ C) (hCD : C ≤ D) (m f : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH D m f b := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH
  apply Real.rpow_le_rpow_of_exponent_le hb
  have : (0:ℝ) ≤ (m:ℝ)^2 * f := by positivity
  nlinarith

end GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

open Formalism.HermitianLatticeCounting.LatticeSumBounds in
theorem xiHyp_mono {C D : ℝ} (hC : 1 ≤ C) (hCD : C ≤ D) {k m f : ℕ} {b v NT : ℝ} {Xi : ℕ → ℝ}
    (hb : 1 ≤ b) (hNT : 1 ≤ NT) (h : XiHyp C k m f b v NT Xi) : XiHyp D k m f b v NT Xi := by
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hD0 : (0:ℝ) ≤ D := by linarith
  have hH1 := bigH_one_le C hC0 m f hb
  have hHD1 := bigH_one_le D hD0 m f hb
  have hHm := bigH_mono hC0 hCD m f hb
  refine ⟨fun s hs hsk => ?_, fun s hs => ?_⟩
  · obtain ⟨h0, h1⟩ := h.1 s hs hsk
    refine ⟨h0, h1.trans ?_⟩
    have e1 : bigH C m f b ^ C ≤ bigH D m f b ^ D := rpow_le_rpow_both hH1 hHm hC0 hCD
    have e2 : C ^ (s * k * f) ≤ D ^ (s * k * f) := pow_le_pow_left₀ hC0 hCD _
    exact mul_le_mul e1 e2 (by positivity) (by positivity)
  · obtain ⟨h0, h1⟩ := h.2 s hs
    refine ⟨h0, h1.trans ?_⟩
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have e1 : (C * k) ^ (k * f) ≤ (D * k) ^ (k * f) :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCD hk0) _
    have a1 : 1 ≤ bigH C m f b ^ (C * m) := Real.one_le_rpow hH1 (by positivity)
    have a2 : bigH C m f b ^ (C * m) ≤ bigH D m f b ^ (D * m) :=
      rpow_le_rpow_both hH1 hHm (by positivity) (mul_le_mul_of_nonneg_right hCD hm0)
    have e2 : (bigH C m f b ^ (C * m) * NT) ^ (C * k) ≤ (bigH D m f b ^ (D * m) * NT) ^ (D * k) := by
      apply rpow_le_rpow_both
      · nlinarith
      · exact mul_le_mul_of_nonneg_right a2 (by linarith)
      · positivity
      · exact mul_le_mul_of_nonneg_right hCD hk0
    exact mul_le_mul e1 e2 (by positivity) (by positivity)

open Formalism.HermitianLatticeCounting.LatticeSumBounds in
theorem params_mono {C D K K₀ : ℝ} (hC : 1 ≤ C) (hCD : C ≤ D) (hK : K ≤ K₀) {k m f : ℕ} {b g v NT : ℝ}
    (h : Params C K₀ k m f b g v NT 1) : Params D K k m f b g v NT 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have hlb : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hX : (0:ℝ) ≤ (m:ℝ) ^ 5 * f * Real.log b := by positivity
  refine ⟨h1, h2, h3, h4, h5, ?_, h7, h8, h9, ?_, le_rfl, ?_⟩
  · have := mul_le_mul_of_nonneg_right hK hX
    nlinarith
  · refine h10.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_)
    have : (0:ℝ) ≤ (m:ℝ) * f := by positivity
    nlinarith
  · have : (0:ℝ) ≤ D := by linarith
    exact Real.one_le_exp (by positivity)

end GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

theorem gam_absorb {C Gam : ℝ} (hC : 0 ≤ C) {k f : ℕ} (hf : 1 ≤ f) (hG : Gam ≤ Real.exp ((k : ℝ) / 8)) :
    C ^ (k * f) * Gam ≤ (Real.exp 1 * C) ^ (k * f) := by
  rw [mul_pow, ← Real.exp_nat_mul, mul_one, mul_comm (Real.exp _)]
  refine mul_le_mul_of_nonneg_left (hG.trans (Real.exp_le_exp.2 ?_)) (by positivity)
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  push_cast
  nlinarith

open Formalism.HermitianLatticeCounting.LatticeSumBounds in
theorem ndRow_mono {C Gam : ℝ} (hC : 1 ≤ C) {k m f s : ℕ} {b g v : ℝ} {Xi : ℕ → ℝ}
    (hf : 1 ≤ f) (hb : 1 ≤ b) (hg : 0 < g) (hv : 0 ≤ v) (hXi : 0 ≤ Xi s)
    (hG : Gam ≤ Real.exp ((k : ℝ) / 8)) :
    ndRow C k m f s b g v Gam Xi ≤ ndRow (Real.exp 1 * C) k m f s b g v 1 Xi := by
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hCD : C ≤ Real.exp 1 * C := le_mul_of_one_le_left hC0 (Real.one_le_exp (by norm_num))
  have hD0 : (0:ℝ) ≤ Real.exp 1 * C := by linarith
  have hH1 := bigH_one_le C hC0 m f hb
  have hHm := bigH_mono hC0 hCD m f hb
  have hHDpos : 0 < bigH (Real.exp 1 * C) m f b := lt_of_lt_of_le zero_lt_one (hH1.trans hHm)
  have hHCpos : 0 < bigH C m f b := lt_of_lt_of_le zero_lt_one hH1
  have e0 : 0 ≤ (2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s := by positivity
  have eH : bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) ≤
      bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2) := by
    apply rpow_le_rpow_both hH1 hHm (by positivity)
    have : (0:ℝ) ≤ ((s : ℝ) + m) * (m : ℝ) ^ 2 := by positivity
    nlinarith
  have eP : (C * s * f) ^ (6 * s * f) ≤ (Real.exp 1 * C * s * f) ^ (6 * s * f) := by
    apply pow_le_pow_left₀ (by positivity)
    have : (0:ℝ) ≤ (s : ℝ) * f := by positivity
    nlinarith
  have eG := gam_absorb hC0 hf hG (k := k)
  unfold ndRow
  calc (2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s * C ^ (k * f) *
        bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) * Gam
      = ((2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s) * (C ^ (k * f) * Gam) *
        bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) := by ring
    _ ≤ ((2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s) * (Real.exp 1 * C) ^ (k * f) *
        bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2) *
        (Real.exp 1 * C * s * f) ^ (6 * s * f) := by
      have hH0 : 0 ≤ bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) :=
        le_trans zero_le_one (Real.one_le_rpow hH1 (by positivity))
      gcongr
    _ = _ := by ring

open Formalism.HermitianLatticeCounting.LatticeSumBounds in
theorem degRow_mono {C Gam : ℝ} (hC : 1 ≤ C) {k m f s : ℕ} {b g v : ℝ} {Xi : ℕ → ℝ}
    (hf : 1 ≤ f) (hb : 1 ≤ b) (hg : 0 < g) (hv : 0 ≤ v) (hXi : 0 ≤ Xi s)
    (hG : Gam ≤ Real.exp ((k : ℝ) / 8)) :
    degRow C k m f s b g v Gam Xi ≤ degRow (Real.exp 1 * C) k m f s b g v 1 Xi := by
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hCD : C ≤ Real.exp 1 * C := le_mul_of_one_le_left hC0 (Real.one_le_exp (by norm_num))
  have hD0 : (0:ℝ) ≤ Real.exp 1 * C := by linarith
  have hH1 := bigH_one_le C hC0 m f hb
  have hHm := bigH_mono hC0 hCD m f hb
  have hHDpos : 0 < bigH (Real.exp 1 * C) m f b := lt_of_lt_of_le zero_lt_one (hH1.trans hHm)
  have hHCpos : 0 < bigH C m f b := lt_of_lt_of_le zero_lt_one hH1
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hb
  have e0 : 0 ≤ (2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s := by positivity
  have eH : bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) ≤
      bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2) := by
    apply rpow_le_rpow_both hH1 hHm (by positivity)
    have : (0:ℝ) ≤ ((s : ℝ) + m) * (m : ℝ) ^ 2 := by positivity
    nlinarith
  have eP : (C * s * f) ^ (6 * s * f) ≤ (Real.exp 1 * C * s * f) ^ (6 * s * f) := by
    apply pow_le_pow_left₀ (by positivity)
    have : (0:ℝ) ≤ (s : ℝ) * f := by positivity
    nlinarith
  have eE : Real.exp (C * (m : ℝ) ^ 6 * f * Real.log b) ≤
      Real.exp (Real.exp 1 * C * (m : ℝ) ^ 6 * f * Real.log b) := by
    apply Real.exp_le_exp.2
    have : (0:ℝ) ≤ (m : ℝ) ^ 6 * f * Real.log b := by positivity
    nlinarith
  have eQ : (C / k) ^ (k * f) ≤ (Real.exp 1 * C / k) ^ (k * f) := by
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_right hCD (Nat.cast_nonneg k)
  have eG := gam_absorb hC0 hf hG (k := k)
  have hH0 : 0 ≤ bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) :=
    le_trans zero_le_one (Real.one_le_rpow hH1 (by positivity))
  unfold degRow
  calc (2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s * C ^ (k * f) *
        bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) * Gam *
        Real.exp (C * (m : ℝ) ^ 6 * f * Real.log b) * (C / k) ^ (k * f)
      = ((2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s) * (C ^ (k * f) * Gam) *
        bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) *
        Real.exp (C * (m : ℝ) ^ 6 * f * Real.log b) * (C / k) ^ (k * f) := by ring
    _ ≤ ((2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s) * (Real.exp 1 * C) ^ (k * f) *
        bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2) *
        (Real.exp 1 * C * s * f) ^ (6 * s * f) *
        Real.exp (Real.exp 1 * C * (m : ℝ) ^ 6 * f * Real.log b) * (Real.exp 1 * C / k) ^ (k * f) := by
      gcongr
    _ = _ := by ring

end GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg


open Formalism.HermitianLatticeCounting.LatticeSumBounds in
theorem corankSums_expLoss : ∀ C : ℝ, 1 ≤ C → ∃ K₀ : ℝ, ∀ (k m f : ℕ) (b g v NT Gam : ℝ) (Xi : ℕ → ℝ),
    Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ k m f b g v NT 1 → Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C k m f b v NT Xi → 0 ≤ Gam →
    Gam ≤ Real.exp ((k : ℝ) / 8) →
    ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k m f s b g v Gam Xi ≤ (Real.sqrt g)⁻¹ ^ (k * f) ∧
    ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k m f s b g v Gam Xi ≤
      Real.exp (-((k : ℝ) * f * Real.log k) / 2) := by
  intro C hC
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hCD : C ≤ Real.exp 1 * C := le_mul_of_one_le_left hC0 (Real.one_le_exp (by norm_num))
  have hD : 1 ≤ Real.exp 1 * C := hC.trans hCD
  obtain ⟨K1, H1⟩ := Formalism.HermitianLatticeCounting.P.sumNondegenerateRowsLe (Real.exp 1 * C) hD
  obtain ⟨K2, H2⟩ := Formalism.HermitianLatticeCounting.P.sumDegenerateRowsLe (Real.exp 1 * C) hD
  refine ⟨max K1 K2, ?_⟩
  intro k m f b g v NT Gam Xi hP hXi _hG0 hG
  obtain ⟨hm4, hmf, hfk, hb2, hg8, -, hv1, -, hNT1, -⟩ := id hP
  have hb1 : (1:ℝ) ≤ b := by linarith
  have hf : 1 ≤ f := by omega
  have hk : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hkb : 0 < (k:ℝ) * b := mul_pos (by linarith) (by linarith)
  have hg : 0 < g := lt_of_lt_of_le (pow_pos hkb 8) hg8
  have hv : (0:ℝ) ≤ v := by linarith
  have P1 := params_mono hC hCD (le_max_left K1 K2) hP
  have P2 := params_mono hC hCD (le_max_right K1 K2) hP
  have X' := xiHyp_mono hC hCD hb1 hNT1 hXi
  have hXs : ∀ s ∈ Finset.Icc 2 k, 0 ≤ Xi s := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    by_cases h2 : s + 2 ≤ k
    · exact (hXi.1 s hs.1 h2).1
    · exact (hXi.2 s (by omega)).1
  refine ⟨?_, ?_⟩
  · refine le_trans (Finset.sum_le_sum fun s hs => ?_) (H1 k m f b g v NT 1 Xi P1 X')
    exact ndRow_mono hC hf hb1 hg hv (hXs s hs) hG
  · have E2 := H2 k m f b g v NT 1 Xi P2 X'
    rw [one_pow, inv_one, mul_one] at E2
    refine le_trans (Finset.sum_le_sum fun s hs => ?_) E2
    exact degRow_mono hC hf hb1 hg hv (hXs s hs) hG

end GlobalTheory.Core.Deg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankTwoCountBoundsOfRowCountBoundsUniform
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Deg

theorem corankTwoCountBounds_of_rowCountBoundsUniform : ∀ S : Set ℝ, CntOn S → CountBoundOn S := by
  intro S h Cg cb Cu cT CT
  obtain ⟨c3, cH, cS, c4, thr, hthr⟩ := h Cg cb Cu cT CT
  exact ⟨c3, cH, thr, fun C0 hC0 C' Cl h1 h2 D large₂ u =>
    ⟨(hthr C0 hC0 C' Cl h1 h2 D large₂ u).1, (hthr C0 hC0 C' Cl h1 h2 D large₂ u).2.1⟩⟩

end GlobalTheory.Core.Deg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegenerateCollisionRowBoundAtParams
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Deg

theorem rowsDeg_at_record : ∀ CT cH cV Ca C2 Ch c C : ℝ, 1 ≤ c → CT ≤ c → |cH| + 2 ≤ c → |cV| + 2 ≤ c → 0 ≤ Ch → c ≤ C → 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C → 2 * C2 ≤ C → |Ca| ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), 3 * |C2| ≤ C' → Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 c → UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH → UnitaryVolumeMass.stVol D large₂ T u u 1 Z C' Cl Cg cb Cu cT CT C0 1 cV → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 (9 * c + 3) Ca C2 Ch 1 → SmallAt D large₂ C' Cl Cg cb Cu cT CT C0 1 → BridgeLemma.TermPtsTie T Z → @BridgeLemma.LatticeDeterminantFactorization D T u u → BridgeLemma₂.wordPairEntriesInLattice T u u → BridgeLemma.RowsDeg T Z C := by
  intro CT cH cV Ca C2 Ch c C k2 hCT k3 k4 hCh hcC hCsq1 hC2 hCa D large₂ u T Z C' Cl Cg cb Cu cT C0 h3C hH hC3 hHH hV hA hS hTP hG0 hE
  have hc0 : 0 ≤ c := by linarith
  have hC1 : 1 ≤ C := k2.trans hcC
  have hCsq : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2 := by nlinarith
  have hHHc : UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 c :=
    BridgeLemma₂.rows_stHH_mono (by linarith [le_abs_self cH]) (by linarith [neg_abs_le cH]) hHH
  have hK := BridgeLemma₂.rows_KBound_of Z hH hHHc k2 hCT
  have hr0 : (0 : ℝ) ≤ D.R.rS := by positivity
  have hm2 : (2 : ℝ) ≤ D.R.m := by rw [BridgeLemma₂.rows_m_cast]; linarith
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast BridgeLemma₂.rows_f_pos D
  have hL1 : 1 ≤ large₂.sc.L := BridgeLemma.d_one_le_L D large₂
  have hkm : (D.R.m : ℝ) + 3 ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  have hk5 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := hH.1.1.2.1
  have ha2 : |C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2 ≤ D.R.k := by
    refine le_trans ?_ hk5
    have e1 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e4 : (D.R.m : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h5 : 0 ≤ (D.R.m : ℝ) ^ 5 := by positivity
    have e2 : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
      nlinarith [mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ) - 1),
        mul_nonneg (mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ))) (by linarith : 0 ≤ large₂.sc.L - 1)]
    have hab := abs_nonneg C2
    have hP : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by linarith
    calc |C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2
        = |C2| * ((D.R.m : ℝ) ^ 2 + 2 * (D.R.m : ℝ) ^ 4) := by ring
      _ ≤ |C2| * (3 * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)) :=
          mul_le_mul_of_nonneg_left (by linarith) hab
      _ = (3 * |C2|) * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by ring
      _ ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := mul_le_mul_of_nonneg_right h3C hP
      _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 4 * (c * D.R.k) + 4 * BridgeLemma₂.pairCountExponent D c D.R.k +
    4 * (c * (D.R.rS : ℝ) ^ 2) + (|C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2) / 2 +
    12 * ((D.R.rS : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    rw [hadef]
    have := BridgeLemma₂.pairCountExponent_nonneg D hc0 D.R.k
    positivity
  have hqb := BridgeLemma₂.rows_q_bound (m := D.R.m) (k := D.R.k) (r := D.R.rS) (c := c)
    (cf := Cnt.cF D.R.f) (a2 := |C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2)
    (BridgeLemma₂.rows_m_cast _) hr0 hkm hc0 (BridgeLemma₂.rows_cF_le hH) ha2
  have hqb' : ((D.R.rS : ℝ) + 1) * a + 1 ≤ (9 * c + 3) * D.R.k * (D.R.m : ℝ) ^ 2 := by
    rw [hadef]; unfold BridgeLemma₂.pairCountExponent; exact hqb
  have hra0 : 0 ≤ ((D.R.rS : ℝ) + 1) * a := by positivity
  have hyp : BridgeLemma₂.rows_Hyps Z C' Cl Cg cb Cu cT CT C0 1 c (9 * c + 3) Ca C2 Ch 1 1
      ⌈((D.R.rS : ℝ) + 1) * a⌉₊ :=
    { hH := hH
      hC3 := hC3
      hHH := hHHc
      hV := BridgeLemma₂.rows_stVol_mono _ (by linarith [le_abs_self cV]) (by linarith [neg_abs_le cV]) hV
      hDEC := hA.2.2
      ha := hS.1
      hb := hS.2.1
      hp := hA.1
      hpp := hA.2.1
      h6 := hS.2.2.1
      hδ := zero_le_one
      hThA := BridgeLemma.word_theorem_a_admissible D u u
      hT := hTP
      hG0 := hG0
      hE := hE
      hc := hc0
      hCh := hCh
      hdim := BridgeLemma₂.rows_dim_pos Z hH.1 (hS.2.2.2.2 hH.1 u)
      hq := by linarith [(Nat.ceil_lt_add_one hra0).le] }
  refine BridgeLemma₂.rows_RowsDeg_record _ hyp hK k2 hcC hC1 hCsq hC2 hCa ?_
  rw [le_div_iff₀ (by positivity)]
  have h1 := Nat.le_ceil (((D.R.rS : ℝ) + 1) * a)
  have h2 : (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 ≤
      (|C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2) / 2 := by
    have := le_abs_self C2
    gcongr
  calc _ ≤ a * ((D.R.rS : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hadef]; linarith
    _ = ((D.R.rS : ℝ) + 1) * a := by ring
    _ ≤ _ := h1

end GlobalTheory.Core.Deg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingZetaValueAtEisensteinHolomorphicPoint
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open Filter Topology Set Metric GlobalTheory.Eis

namespace GlobalTheory.Eis

theorem zetaHolValueAt_of_heightBounds (l1 : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (c : ℕ), ∀ g₁ g₂ : GA D V,
    GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c) (l2 : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle) (m : Measure (GA D V)), m.IsHaarMeasure →
    ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → ∀ (C' : ℝ) (c : ℕ),
    (∀ g₁ g₂ : GA D V, GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C' * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c) →
    ∀ (C : ℝ) (N : ℕ), ∃ bound : AutQ V × AutQ V → ℝ, Integrable bound ((autMeasure V m).prod (autMeasure V m)) ∧
      ∀ E : GA D (dblSp V) → ℂ, LeftInv (GQ (dblSp V)) E → (∀ g, ‖E g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) →
        ∀ q, ‖GlobalTheory.Eis.dblIntegrandQ V μ E f₁ f₂ q‖ ≤ bound q) : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (m : Measure (GA D V)), m.IsHaarMeasure → ∀ (Φ : ℂ → GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisContinues V Φ → (∀ g, AnalyticOnNhd ℂ (GlobalTheory.Eis.eisSer V Φ g) (rightOf (V.rank / 2))) → (∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt V Φ s₀ k) → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → GlobalTheory.Eis.IsZetaFamily V μ m Φ f₁ f₂ → ∀ (s₀ : ℂ) (E₀ : GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisValueAt V Φ s₀ E₀ → GlobalTheory.Eis.DblConv V μ m E₀ f₁ f₂ ∧ GlobalTheory.Eis.ZetaHolValueAt V μ m Φ f₁ f₂ s₀ (GlobalTheory.Eis.dblInt V μ m E₀ f₁ f₂) := by
  intro D V μ hμ m hm Φ hE ha hreg f₁ f₂ h₁ h₂ hZ s₀ E₀ hv
  obtain ⟨C', c, hio⟩ := l1 D V
  have key : ∀ (H : ℂ → GA D (dblSp V) → ℂ) (z : ℂ) (r : ℝ), 0 < r →
      (∀ s ∈ ball z r, LeftInv (GQ (dblSp V)) (H s)) →
      (∀ g, DifferentiableOn ℂ (H · g) (ball z r)) →
      ContinuousOn (fun x : ℂ × GA D (dblSp V) => H x.1 x.2) (ball z r ×ˢ univ) →
      (∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball z r, ∀ g, ‖H s g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) →
      (∀ s ∈ ball z r, DblConv V μ m (H s) f₁ f₂) ∧
        DifferentiableOn ℂ (fun s => dblInt V μ m (H s) f₁ f₂) (ball z r) := by
    rintro H z r hr hinv hd hc ⟨C, N, hb⟩
    obtain ⟨bound, hbi, hbd⟩ := l2 D V μ m hm f₁ f₂ h₁ h₂ C' c hio C N
    have hcont : ∀ s ∈ ball z r, Continuous (H s) := fun s hs =>
      hc.comp_continuous (f := fun g => (s, g)) (by fun_prop) fun g => ⟨hs, trivial⟩
    have hli : ∀ s ∈ ball z r, LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ (H s) f₁ f₂) := fun s hs =>
      leftInv_dblIntegrand hμ (hinv s hs) h₁.1 h₂.1
    have hmeas : ∀ s ∈ ball z r, AEStronglyMeasurable (dblIntegrandQ V μ (H s) f₁ f₂)
        ((autMeasure V m).prod (autMeasure V m)) := by
      intro s hs
      have e' : dblIntegrandQ V μ (H s) f₁ f₂ =
          dblIntegrand V μ (H s) f₁ f₂ ∘ Prod.map (sec (GQ V)) (sec (GQ V)) :=
        funext fun q => (congrArg _ (Prod.ext (mk_sec q.1) (mk_sec q.2)).symm).trans (dblIntegrandQ_mk (hli s hs) _ _)
      rw [e']
      exact ((continuous_dblIntegrand hμ (hcont s hs) h₁.continuous h₂.continuous).measurable.comp
        (measurableEmbedding_sec.measurable.prodMap measurableEmbedding_sec.measurable)).aestronglyMeasurable
    refine ⟨fun s hs => ⟨hli s hs, hbi.mono' (hmeas s hs) (ae_of_all _ fun q => hbd (H s) (hinv s hs) (hb s hs) q)⟩, ?_⟩
    have := GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated
      (μ := (autMeasure V m).prod (autMeasure V m)) (F := fun q s => dblIntegrandQ V μ (H s) f₁ f₂ q)
      (isOpen_ball (x := z) (ε := r)) hmeas
      (ae_of_all _ fun q => by
        simp only [dblIntegrandQ, dblIntegrand]
        exact (((hd _).mul_const _).mul_const _).mul_const _)
      fun x hx => ⟨ball z r, isOpen_ball.mem_nhds hx, bound, hbi,
        ae_of_all _ fun q y hy => hbd (H y) (hinv y hy) (hb y hy) q⟩
    exact this.1
  have hinvE : ∀ s, LeftInv (GQ (dblSp V)) (eisCont V Φ s) := fun s => hE.1.leftInv_eisLaurent s 0
  set Z : ℂ → ℂ := fun s => dblInt V μ m (eisCont V Φ s) f₁ f₂ with hZdef
  have hmer : ∀ s₁, MeromorphicAt Z s₁ := by
    intro s₁
    obtain ⟨k, r, H, hr, e, hd, hc, C, N, hb⟩ := hreg s₁
    have hinvH : ∀ s ∈ ball s₁ r, LeftInv (GQ (dblSp V)) (H s) := by
      intro s hs γ hγ g
      rcases eq_or_ne s s₁ with rfl | h0
      · have t1 := ((hd (γ * g)).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := {s}ᶜ))
        have t2 := ((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := {s}ᶜ))
        refine tendsto_nhds_unique t1 (t2.congr' ?_)
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s hr)] with w h1 h2
        rw [e w h2 h1, e w h2 h1, hinvE w γ hγ g]
      · rw [e s hs h0, e s hs h0, hinvE s γ hγ g]
    have han : AnalyticAt ℂ (fun s => dblInt V μ m (H s) f₁ f₂) s₁ :=
      (key H s₁ r hr hinvH hd hc ⟨C, N, hb⟩).2.analyticAt (ball_mem_nhds _ hr)
    have hm1 : MeromorphicAt (fun s => ((s - s₁) ^ k)⁻¹ * dblInt V μ m (H s) f₁ f₂) s₁ := by
      have : MeromorphicAt (fun s : ℂ => s - s₁) s₁ := (MeromorphicAt.id s₁).sub (MeromorphicAt.const _ _)
      exact (this.pow k).inv.mul han.meromorphicAt
    refine hm1.congr ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₁ hr)] with w h1 h2
    have e1 : eisCont V Φ w = ((w - s₁) ^ k)⁻¹ • H w := by
      funext g
      rw [Pi.smul_apply, e w h2 h1 g, smul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ (sub_ne_zero.2 h1)), one_mul]
    have e2 := dblInt_smul (V := V) (μ := μ) (m := m) (E := H w) (f₁ := f₁) (f₂ := f₂) ((w - s₁) ^ k)⁻¹ 1 1
    simp only [one_smul, map_one, mul_one] at e2
    simp only [Z, e1, e2]
  have hext : IsMerExt (zeta V μ m Φ f₁ f₂) univ Z := by
    refine ⟨isRightDomain_univ, fun s _ => hmer s, (V.rank : ℝ) / 2, fun s hs => ?_⟩
    have : eisCont V Φ s = eis V (Φ s) := funext fun g => eqOn_cont (ha g) hs
    simp only [Z, zeta, this]
  obtain ⟨k, hk⟩ := hreg s₀
  obtain ⟨r, hr, hd, hc, C, N, hb⟩ := hk.of_eisValueAt hv
  obtain ⟨hconv, hdiff⟩ := key (eisCont V Φ) s₀ r hr (fun s _ => hinvE s) hd hc ⟨C, N, hb⟩
  have e0 := hv.eisCont_eq
  refine ⟨e0 ▸ hconv s₀ (mem_ball_self hr), hZ, Z, hext.isExtAt trivial, hdiff.analyticAt (ball_mem_nhds _ hr), ?_⟩
  simp only [Z, e0]

theorem zetaHolValueAt_of_eisValueAt : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (m : Measure (GA D V)), m.IsHaarMeasure → ∀ (Φ : ℂ → GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisContinues V Φ → (∀ g, AnalyticOnNhd ℂ (GlobalTheory.Eis.eisSer V Φ g) (rightOf (V.rank / 2))) → (∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt V Φ s₀ k) → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → GlobalTheory.Eis.IsZetaFamily V μ m Φ f₁ f₂ → ∀ (s₀ : ℂ) (E₀ : GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisValueAt V Φ s₀ E₀ → GlobalTheory.Eis.DblConv V μ m E₀ f₁ f₂ ∧ GlobalTheory.Eis.ZetaHolValueAt V μ m Φ f₁ f₂ s₀ (GlobalTheory.Eis.dblInt V μ m E₀ f₁ f₂) :=
  zetaHolValueAt_of_heightBounds _root_.GlobalTheory.Cont.HeightIo.height_io_bound _root_.GlobalTheory.Core.Rk.Dom.exists_integrable_bound_dblIntegrandQ

end GlobalTheory.Eis
end

