module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0017
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0424
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0227
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0423
public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsFD
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeRatioEqVandermondeRatioAlongLine
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DegLine

open Formalism.QuantumDeterminants Formalism.MainNotions.S

theorem gap_near {N : ℕ} (ε : Fin N → Bool) (l ν : Fin N → ℝ) (G ρ : ℝ) (hg : GapAtLeast ε l G)
    (hν : l1dist ν l ≤ ρ) : GapAtLeast ε ν (G - 2 * ρ) := by
  intro a b hab
  have hco : ∀ j, |ν j - l j| ≤ ρ := fun j =>
    le_trans (Finset.single_le_sum (f := fun j => |ν j - l j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)) hν
  have h1 := hg a b hab
  have h2 := hco a
  have h3 := hco b
  have h4 : |l a - l b| ≤ |ν a - ν b| + |ν a - l a| + |ν b - l b| := by
    have e : l a - l b = (ν a - ν b) - (ν a - l a) + (ν b - l b) := by ring
    rw [e]
    exact le_trans (abs_add_le _ _) (by have := abs_sub (ν a - ν b) (ν a - l a); linarith)
  linarith

theorem gap_lamD (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (τ : D.what₂.Tau) :
    GapAtLeast (epsSH D.R) (lamD D τ) (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbnd, _, _, _, _, hstep, _, _, _, hCl⟩ := hH.1
  have hL := one_lt_scL large₂
  have hG0 : 0 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have : 0 ≤ Cl := hCl.le
    have : 0 ≤ large₂.sc.L := by linarith
    positivity
  have hv : ∀ l, 1 ≤ l → l ≤ D.R.k - 1 → 0 ≤ vOne D τ l := fun l h1 h2 => (hH.2.1.1 τ l h1 h2).1
  have hm := D.R.two_le_m
  have hb1 : 0 ≤ bOne D τ 1 := by
    have h := (hbnd τ 1 le_rfl (by omega)).1
    exact le_trans (le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) (le_max_left _ _)) h
  have g := gapAtLeast_of τ _ hG0 hv hb1 (hstep τ)
  intro a b hab
  exact g (Fin.cast (dimS_eq D.R) a) (Fin.cast (dimS_eq D.R) b) hab

theorem deg_eq_fdegHC (D : D7) (ht : cdScaleTie D) {W : LocW D.R.k D.R.rS}
    (l : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (hA : GoodS D l A) (h : ℝ)
    (hg : GapAtLeast (epsSH D.R) l h) (hth : Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < h) : A.deg = fdegHC l := by
  obtain ⟨P, hP, hd⟩ := hA.2.2.2.2.2.2.2.2.2.2
  obtain ⟨Q, ⟨hQ, -⟩, hDS⟩ := hA.2.1
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQd
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQd
  let u : (Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)ˣ := ⟨Q * P⁻¹, P * Q⁻¹,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹, hPP', Matrix.one_mul, hQQ],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q⁻¹, hQQ', Matrix.one_mul, hPP]⟩
  let a : Formalism.REAL.UJ (epsSH D.R) := ⟨u, GlobalTheory.FormalDegreeDatum.inUJ_of_cayley _ P Q _ hP.1 hP.2 hQ.2⟩
  have hsc := (GlobalTheory.Mem.Vol.cdScaleTie_iff D).1 ht
  obtain ⟨a1, b1, hab⟩ := Formalism.MainNotions.TheoremBConstants.epsSH_both D
  have ht1 : ∃ x, epsSH D.R x = true := by
    cases h1 : epsSH D.R a1
    · exact ⟨b1, by cases h2 : epsSH D.R b1 <;> simp_all⟩
    · exact ⟨a1, h1⟩
  have hf1 : ∃ x, epsSH D.R x = false := by
    cases h1 : epsSH D.R a1
    · exact ⟨a1, h1⟩
    · exact ⟨b1, by cases h2 : epsSH D.R b1 <;> simp_all⟩
  have hF := _root_.GlobalTheory.FdegGap.fdeg_gap D.cd D.s.cdScale hsc _ (epsSH D.R) l h hA.1 ht1 hf1 hg hth A.H
    (fun g => A.σ (Q⁻¹ * g * Q)) hDS
  haveI := hDS.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : A.H)
  have h2 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj _ (fun g => A.σ (P⁻¹ * g * P))
    (fun g => A.σ (Q⁻¹ * g * Q)) a (fun g => by
      have e : umat (a * g * a⁻¹) = Q * P⁻¹ * umat g * (P * Q⁻¹) := rfl
      have e2 : Q⁻¹ * (Q * P⁻¹ * umat g * (P * Q⁻¹)) * Q =
          (Q⁻¹ * Q) * (P⁻¹ * umat g * P) * (Q⁻¹ * Q) := by
        simp only [Matrix.mul_assoc]
      simp only [e, e2, hQQ', Matrix.one_mul, Matrix.mul_one]) hDS.2.2.1 A.deg hd w hw
  have h3 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj _ (fun g => A.σ (Q⁻¹ * g * Q))
    (fun g => A.σ (Q⁻¹ * g * Q)) 1 (fun g => by simp) hDS.2.2.1 (fdegHC l) hF w hw
  exact h2.symm.trans h3

theorem deg_eq_near (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 Cn : ℝ} (hCl : 2 * |Cn| + 8 ≤ Cl)
    (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (ht : cdScaleTie D) (τ : D.what₂.Tau) {W : LocW D.R.k D.R.rS}
    (ν : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (hν : l1dist ν (lamD D τ) ≤ |Cn| * (D.R.r : ℝ) ^ 4 + D.R.r)
    (A : LocS W) (hA : GoodS D ν A) : A.deg = fdegHC ν := by
  refine deg_eq_fdegHC D ht ν A hA _ (gap_near _ _ _ _ _ (gap_lamD D large₂ hH τ) hν) ?_
  obtain ⟨_, _, hmf, _⟩ := hH.1
  have hL := one_lt_scL large₂
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr6 : (6 : ℝ) ≤ D.R.r := by
    have : 6 ≤ D.R.r := by unfold Formalism.BasicNotions.Ranks.r; omega
    exact_mod_cast this
  have hthr := Formalism.MainNotions.GapDS.thrE_le (epsSH D.R) (by rw [Formalism.MainNotions.BridgeLemma₂.deg_cast_r]; linarith)
  rw [Formalism.MainNotions.BridgeLemma₂.deg_cast_r] at hthr
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ D.R.r := by linarith
  have h419 : (D.R.r : ℝ) ^ 4 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have h319 : (D.R.r : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have h119 : (D.R.r : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by
    simpa using pow_le_pow_right₀ hn1 (show 1 ≤ 19 by norm_num)
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf
  have hfl : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 * large₂.sc.L := by nlinarith
  have hCl0 : 0 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_nonneg (by linarith [abs_nonneg Cn]) (by positivity)
  have e1 : Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have := mul_le_mul_of_nonneg_left hfl hCl0
    have e : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L = Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) := by
      ring
    rw [e]; linarith
  have e2 : (2 * |Cn| + 8) * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 :=
    mul_le_mul_of_nonneg_right hCl (by positivity)
  have e3 : |Cn| * (D.R.r : ℝ) ^ 4 ≤ |Cn| * (D.R.r : ℝ) ^ 19 := mul_le_mul_of_nonneg_left h419 (abs_nonneg _)
  nlinarith

theorem deg_VandLine_of_gap : ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C1 : ℝ),
    thr ≤ C' → thr ≤ Cl → Ties D → Formalism.MainNotions.BridgeLemma₂.deg_VandLine D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 := by
  intro Cn
  refine ⟨2 * |Cn| + 8, fun D large₂ C' Cl Cg cb Cu cT CT C0 C1 _ hCl hT => ?_⟩
  intro hH τ w w' _ θ _ W _ lam' hl A hA I s hs A' hA'
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by
    have : D.R.k ≤ D.R.r := by unfold Formalism.BasicNotions.Ranks.r; omega
    exact_mod_cast this
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by
    have : D.R.m ≤ D.R.r := by unfold Formalism.BasicNotions.Ranks.r; omega
    exact_mod_cast this
  have hn : (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 4 := by
    calc (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) * (D.R.r : ℝ) ^ 3 :=
          mul_le_mul hkr (pow_le_pow_left₀ (by positivity) hmr 3) (by positivity) (by positivity)
      _ = (D.R.r : ℝ) ^ 4 := by ring
  have hcard : (I.card : ℝ) ≤ D.R.r := by
    rw [← Formalism.MainNotions.BridgeLemma₂.deg_cast_r]
    have : I.card ≤ 2 * D.R.rS + D.R.k + 1 := by
      have := Finset.card_le_univ I
      rwa [Fintype.card_fin] at this
    exact_mod_cast this
  have hl' : Cn * D.R.k * (D.R.m : ℝ) ^ 3 ≤ |Cn| * (D.R.r : ℝ) ^ 4 := by
    have e : Cn * D.R.k * (D.R.m : ℝ) ^ 3 = Cn * ((D.R.k : ℝ) * (D.R.m : ℝ) ^ 3) := by ring
    rw [e]
    exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self Cn) (by positivity))
      (mul_le_mul_of_nonneg_left hn (abs_nonneg _))
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have h1 : l1dist lam' (lamD D τ) ≤ |Cn| * (D.R.r : ℝ) ^ 4 + D.R.r := by linarith
  have h2 : l1dist (lam' + s • epsI I) (lamD D τ) ≤ |Cn| * (D.R.r : ℝ) ^ 4 + D.R.r :=
    le_trans (Formalism.MainNotions.BridgeLemma.l1_distance_sign_step _ _ s hs I) (by linarith)
  rw [deg_eq_near D large₂ hCl hH hT.cdScale_tie τ lam' h1 A hA,
    deg_eq_near D large₂ hCl hH hT.cdScale_tie τ _ h2 A' hA']

end GlobalTheory.DegLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalTermLiesOverLocalDatumAfterIsometry
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver

namespace GlobalTheory.LocOver.GlobOver

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

theorem uni_mul {K : Type} [CommRing K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : Uni A) (hB : Uni B) :
    Uni (A * B) := by
  obtain ⟨hA0, hA1⟩ := hA
  obtain ⟨hB0, hB1⟩ := hB
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [hA0 a c h, zero_mul]
    · rw [hB0 c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA1, hB1, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hA0 a c h, zero_mul]
      · rw [hB0 c a h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h

theorem tri_trans {K W : Type} [CommRing K] [AddCommGroup W] [Module K W] {n : ℕ} {f g h : Fin n → W}
    (h1 : Tri K f g) (h2 : Tri K g h) : Tri K f h := by
  obtain ⟨A, hA, hAc⟩ := h1
  obtain ⟨B, hB, hBc⟩ := h2
  have hAc' : ∀ b, g b = ∑ a, A a b • f a := hAc
  have hBc' : ∀ b, h b = ∑ a, B a b • g a := hBc
  refine ⟨A * B, uni_mul hA hB, fun b => ?_⟩
  rw [hBc' b]
  simp only [hAc', Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]

theorem tri_map {K W W' : Type} [CommRing K] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W'] {n : ℕ}
    (φ : W →ₗ[K] W') {f g : Fin n → W} (h : Tri K f g) : Tri K (fun a => φ (f a)) (fun a => φ (g a)) := by
  obtain ⟨A, hA, hc⟩ := h
  have hc' : ∀ b, g b = ∑ a, A a b • f a := hc
  exact ⟨A, hA, fun b => by simp only [hc' b, map_sum, map_smul]⟩

end Mat

section Loc

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ img g Λ ↔ ∃ y ∈ Λ, g y = x := by
  unfold img
  exact Submodule.mem_map

theorem span_map_le (g : V ≃ₗ[E] V) (S : Set V) :
    ∀ v ∈ Submodule.span M.L.O S, g v ∈ Submodule.span M.L.O ((fun x => g x) '' S) := by
  intro v hv
  have h := Submodule.mem_map_of_mem (f := (g : V →ₗ[E] V).restrictScalars M.L.O) hv
  rw [← Submodule.span_image] at h
  exact h

theorem img_selfDual (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} (hΛ : H.IsSelfDual Λ) : H.IsSelfDual (img g Λ) := by
  obtain ⟨hfg, hsp, hdual⟩ := hΛ
  have hg' : ∀ x y, H.h (g x) (g y) = H.h x y := hg
  have hset : ((img g Λ : Submodule M.L.O V) : Set V) = (g : V →ₗ[E] V) '' (Λ : Set V) := by
    ext x
    simp only [SetLike.mem_coe, mem_img, Set.mem_image, LinearEquiv.coe_coe]
  refine ⟨hfg.map _, ?_, fun x => ?_⟩
  · rw [hset, Submodule.span_image, hsp, Submodule.map_top]
    exact LinearEquiv.range g
  · have hx : x ∈ img g Λ ↔ g.symm x ∈ Λ := by
      rw [mem_img]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro h
        exact ⟨_, h, by simp⟩
    rw [hx, hdual (g.symm x)]
    constructor
    · intro h y hy
      obtain ⟨z, hz, rfl⟩ := (mem_img g Λ y).1 hy
      have := h z hz
      rw [← hg' (g.symm x) z, LinearEquiv.apply_symm_apply] at this
      exact this
    · intro h z hz
      rw [← hg' (g.symm x) z, LinearEquiv.apply_symm_apply]
      exact h (g z) ((mem_img g Λ (g z)).2 ⟨z, hz, rfl⟩)

theorem img_frame (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} {r : ℕ} {f : Fin (r + 1) → V} {T : F} (hf : H.IsFrame Λ r f T) :
    H.IsFrame (img g Λ) r (fun b => g (f b)) T := by
  have hg' : ∀ x y, H.h (g x) (g y) = H.h x y := hg
  obtain ⟨⟨hmem, hli, hsp⟩, hiso, hzz, hT⟩ := hf
  refine ⟨⟨fun a => (mem_img g Λ _).2 ⟨f a, hmem a, rfl⟩, hli.map' _ g.ker, ?_⟩, ?_, ?_, hT⟩
  · intro x hx hxs
    obtain ⟨y, hy, rfl⟩ := (mem_img g Λ x).1 hx
    have hr : Set.range (fun b => g (f b)) = (g : V →ₗ[E] V) '' Set.range f :=
      Set.range_comp (⇑(g : V →ₗ[E] V)) f
    have hys : y ∈ Submodule.span E (Set.range f) := by
      rw [hr, Submodule.span_image, Submodule.mem_map] at hxs
      obtain ⟨z, hz, hzy⟩ := hxs
      rwa [← g.injective hzy]
    have h2 := span_map_le (M := M) g (Set.range f) y (hsp y hy hys)
    have hr' : Set.range (fun b => g (f b)) = (fun x => g x) '' Set.range f :=
      Set.range_comp (fun x => g x) f
    rw [hr']
    exact h2
  · intro a b hab
    rw [hg']
    exact hiso a b hab
  · rw [hg']
    exact hzz

theorem smulLat_map (H : HermSp M V) (g : V ≃ₗ[E] V) (c : E) (Λ : Submodule M.L.O V) {x : V}
    (hx : x ∈ H.smulLat c Λ) : g x ∈ H.smulLat c (img g Λ) := by
  unfold HermSp.smulLat at hx ⊢
  refine Submodule.span_mono ?_ (span_map_le (M := M) g _ x hx)
  rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  exact ⟨g v, (mem_img g Λ (g v)).2 ⟨v, hv, rfl⟩, by simp only [map_smul]⟩

private lemma Zhat_comp_unitary (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {r : ℕ}
    (f f' : Fin (r + 1) → V) :
    H.Zhat (fun b => g (f b)) (fun b => g (f' b)) = H.Zhat f f' := by
  have hg' : ∀ x y, H.h (g x) (g y) = H.h x y := hg
  ext a b
  simp only [HermSp.Zhat, Matrix.of_apply, hg']

private lemma Dl_comp_unitary (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {r : ℕ}
    (f f' : Fin (r + 1) → V) (l : ℕ) :
    H.Dl (fun b => g (f b)) (fun b => g (f' b)) l = H.Dl f f' l := by
  simp only [HermSp.Dl, Zhat_comp_unitary H hg]

theorem isTerm_move (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {r : ℕ} {t : Term V M r}
    (ht : H.IsTerm t) : H.IsTerm (move g t) := by
  obtain ⟨hsd, hfr, hfr', hD, hG, hsp⟩ := ht
  refine ⟨img_selfDual H hg hsd, img_frame H hg hfr, img_frame H hg hfr', ?_, ?_, ?_⟩
  · show IsUnit (H.Dl (fun b => g (t.f b)) (fun b => g (t.f' b)) (r + 1))
    rw [Dl_comp_unitary H hg]
    exact hD
  · show H.Gdet (fun b => g (t.f b)) (fun b => g (t.f' b)) t.T t.T' ≠ 0
    simpa only [HermSp.Gdet, Dl_comp_unitary H hg] using hG
  · intro q hq
    obtain ⟨h1, h2, h3⟩ := hsp q hq
    refine ⟨h1, h2, fun b => ?_⟩
    show g (t.f' b) - g (t.f b) ∈ H.smulLat _ (img g t.abelian₂)
    rw [← map_sub]
    exact smulLat_map H g _ t.abelian₂ (h3 b)

end Loc

section Glob

theorem over_local : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F' → Gval (lf D F0) F' ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), IsInCell (ZhatOM (ZhatL (lf D F0) F')) w → ZhatOM (ZhatL F00 F'0) = ptMat w → ∀ (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), AtBase Z p F00 F'0 (Tu D u) (Tu D u') P → ∃ d, Over P d (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) := by
  intro D Z u u' F0 Λ hrow F' hPD hG w F00 F'0 hcell hpt p P hAt
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.L2.SG.GramJoint.Tu_pos D u).ne'
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.L2.SG.GramJoint.Tu_pos D u').ne'
  obtain ⟨-, γ, hγ, hA, hA'⟩ := _root_.GlobalTheory.LocOver.witt_frames_at_point D (lf D F0) F00 F' F'0 w hT hT' hG hcell hpt
  obtain ⟨g, hext, hgU, -, -, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p γ hγ
  obtain ⟨ht0, htri0⟩ := locU_isTerm D Z u u' F0 Λ hrow F' hPD hG p
  have hOK : (Z.M p).OK := (Z.agree p).1
  obtain ⟨A, hAu, hAc⟩ := hA
  obtain ⟨A', hA'u, hA'c⟩ := hA'
  obtain ⟨Ap, hAp, -⟩ := tri_scaled D Z _ _ A hAu hAc
  obtain ⟨Ap', hAp', -⟩ := tri_scaled D Z _ _ A' hA'u hA'c
  have hext' : ∀ x, g (baseChange₂ D p x) = baseChange₂ D p (γ x) := hext
  have hmove : ∀ f : Fin (D.R.rS + 1) → (VS D).V,
      (fun a => g (scaled Z p f a)) = scaled Z p (fun a => γ (f a)) := by
    intro f
    funext a
    simp only [scaled, map_smul, hext']
  set t := locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u') with ht_def
  have hf : Tri (D.s.atP p).Ep P.A.f (move g t).f := by
    rw [hAt.1]
    have h1 : (move g t).f = fun a => g (scaled Z p (frame (lf D F0)) a) := rfl
    rw [h1, hmove (frame (lf D F0))]
    exact ⟨Ap p, hAp p⟩
  have hf' : Tri (D.s.atP p).Ep P.B.f (move g t).f' := by
    rw [hAt.2.1]
    have h1 : Tri (D.s.atP p).Ep (fun a => g (scaled Z p (frame F') a)) (fun a => g (t.f' a)) :=
      tri_map (g : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p) htri0
    rw [hmove (frame F')] at h1
    exact tri_trans ⟨Ap' p, hAp' p⟩ h1
  obtain ⟨d, hd⟩ := _root_.GlobalTheory.LocOver.TermOver.exists_datum (Z.M p) hOK (locH Z p) D.R.rS P (move g t)
    (isTerm_move (locH Z p) hgU ht0) hAt.2.2.1.symm hAt.2.2.2.symm hf hf'
  refine ⟨d, ?_⟩
  unfold Over
  exact ⟨g, hgU, d, (orbit_reps_over (Z.M p) hOK (locH Z p) D.R.rS P).1.refl d, hd⟩

end Glob

end GlobalTheory.LocOver.GlobOver
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataGlobalTermIndependentOfRepresentative
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.RepIndep

open GlobalTheory.LoopC.PairMove GlobalTheory.LoopC.FrEqv

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {Λ : Submodule (𝓞 E) S.V}

theorem xsp_map_of_frame {F₁ F₂ : LFlag S r T'} (f : S.V ≃ₗ[E] S.V) (h : ∀ a, frame F₂ a = f (frame F₁ a)) :
    (Xsp F₁).map (f : S.V →ₗ[E] S.V) = Xsp F₂ := by
  change (Submodule.span E (Set.range F₁.fl.e)).map _ = Submodule.span E (Set.range F₂.fl.e)
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1
  have : (f : S.V →ₗ[E] S.V) ∘ F₁.fl.e = F₂.fl.e := by
    funext b
    have := h b.castSucc
    rw [Formalism.L2.SG.Pf.frame_castSucc_td, Formalism.L2.SG.Pf.frame_castSucc_td] at this
    simp [this]
  rw [this]

theorem iota_of_dc {F : LFlag S r T} {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V} (g : ℕ)
    (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁) (hfr : ∀ a, frame F₂ a = (n * m) (frame F₁ a)) :
    IotaCompat Λ F F₁ F₂ (n * m) g := by
  have hmX : (Xsp F₁).map (m : S.V →ₗ[E] S.V) = Xsp F₁ := nlam_map hm
  have hnmX := xsp_map_of_frame (n * m) hfr
  have hnX : (Xsp F₁).map (n : S.V →ₗ[E] S.V) = Xsp F₂ := by
    refine map_of_mem_iff fun x => ?_
    have e : n x = (n * m) (m.symm x) := by simp [LinearEquiv.mul_apply]
    rw [e, mem_iff_of_map hnmX, mem_iff_of_map (map_symm hmX)]
  have hi : n⁻¹ ∈ NLam Λ F := Formalism.L2.SG.Pf.nlamPf_inv hn
  intro x' hx' l hl
  have e : l - (n * m) x' = n (n⁻¹ l - m x') := by
    rw [map_sub]
    simp [LinearEquiv.mul_apply]
  rw [e, ngx_iff hn.1 (nlam_map hn) hnX g]
  have e2 : n⁻¹ l - m x' = (l - x') + ((n⁻¹ l - l) - (m x' - x')) := by abel
  rw [e2]
  refine (Submodule.add_mem_iff_left _ ?_).symm
  refine Submodule.sub_mem _ ?_ ?_
  · refine Submodule.mem_sup_left (Submodule.mem_sup_right ⟨?_, hi.2.2 l hl.2⟩)
    exact Λ.sub_mem ((aut_mem_iff hi.1 l).2 hl.1) hl.1
  · refine Submodule.mem_sup_right ⟨?_, hm.2.2 x' hx'.2⟩
    exact Λ.sub_mem ((aut_mem_iff hm.1 x').2 hx'.1) hx'.1

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rep_indep : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F₁ → PD D Λ (lf D F0) u' F₂ → Gval (lf D F0) F₁ ≠ 0 → DCRel Λ (lf D F0) F₁ F₂ → ∀ (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), P.RelG (LocNG.theta (Z.M p)) → ∀ d, Over P d (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')) ↔ Over P d (locU Z p Λ (lf D F0) F₂ (Tu D u) (Tu D u')) := by
  intro D Z u u' F0 Λ hΛ F₁ F₂ h1 h2 hG hdc p P hP d
  have key : ∀ A B : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' A → PD D Λ (lf D F0) u' B →
      Gval (lf D F0) A ≠ 0 → DCRel Λ (lf D F0) A B →
      Over P d (locU Z p Λ (lf D F0) A (Tu D u) (Tu D u')) → Over P d (locU Z p Λ (lf D F0) B (Tu D u) (Tu D u')) := by
    intro A B hA hB hGA hAB
    obtain ⟨n, hn, m, hm, hfr, -⟩ := hAB
    exact _root_.GlobalTheory.LocSame.over_same D Z u u' F0 Λ hΛ A B hA hB hGA n ⟨hn.1.1, hn.2.1, hn.2.2⟩ m ⟨hm.1.1, hm.2.1, hm.2.2⟩
      (Formalism.L2.SG.Pf.isAutLam_mul hn.1 hm.1).2 (fun a => hfr a) (iota_of_dc (gS D) hn hm (fun a => hfr a)) p P hP d
  refine ⟨key F₁ F₂ h1 h2 hG hdc, key F₂ F₁ h2 h1 ?_ (Formalism.L2.SG.Pf.dcrel_symm _ _ hdc)⟩
  rw [Formalism.L2.SG.Pf.gval_rel (h := hdc)]
  exact hG

end GlobalTheory.LocOver.RepIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TFrameOfRanksRowThree
section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem tFrame_of_ranksRow_three : ∀ 𝒞 : FamClass,
    (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) →
      Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 := by
  intro 𝒞 h
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := Formalism.L2.SG.OwnFacts.FD.factDsigHC
  haveI : Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram := ⟨GlobalTheory.hermRepUnram⟩
  exact Formalism.L2.SG.Pf.SzHypFam.hTF_of_ranks 3 (𝒞 := 𝒞) h

end GlobalTheory
end

