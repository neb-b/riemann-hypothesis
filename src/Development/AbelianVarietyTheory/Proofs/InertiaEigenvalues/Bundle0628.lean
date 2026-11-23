module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0622
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOMapHaar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem actO_map_haar : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (μ : Measure (WO S T)),
    μ.IsAddHaarMeasure → μ.map (actO S T g h) = μ := by
  intro D S T g h μ hμ
  haveI : BorelSpace (Mx D T.rank S.rank) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have hL : Continuous (fun x : Mx D T.rank S.rank =>
      (HMul.hMul (mt T h) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Mx D T.rank S.rank)) :=
    continuous_const.matrix_mul continuous_id
  have hR : Continuous (fun x : Mx D T.rank S.rank =>
      (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) : Mx D T.rank S.rank)) :=
    continuous_id.matrix_mul continuous_const
  have e : actO S T g h =
      (fun x : Mx D T.rank S.rank =>
        (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) : Mx D T.rank S.rank)) ∘
      (fun x : Mx D T.rank S.rank =>
        (HMul.hMul (mt T h) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Mx D T.rank S.rank)) := rfl
  rw [e, ← Measure.map_map hR.measurable hL.measurable, _root_.GlobalTheory.map_mt_mul_eq D T S.rank h μ hμ]
  exact _root_.GlobalTheory.AdelicModulus.map_mul_right_unitary D S T.rank g⁻¹ μ hμ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BallFnMemAndOneMemOfSubMem
section
open ValuativeRel OnePoint GlobalTheory.LocGL.ProjLine

namespace GlobalTheory.LocGL.ProjLine

variable {k : Type} [Field k] [ValuativeRel k]

theorem Stable.scale_mem {S : Submodule ℂ (OnePoint k → ℂ)} (hS : Stable S) {c : k} (hc : c ≠ 0)
    (α β γ : ℂ) (a r b s : k)
    (h : α • (fun _ => (1 : ℂ)) + β • ballFn a r + γ • ballFn b s ∈ S) :
    α • (fun _ => (1 : ℂ)) + β • ballFn (c * a) (c * r) + γ • ballFn (c * b) (c * s) ∈ S := by
  have hv : 0 < valuation k c := zero_lt_iff.2 (by simpa using hc)
  have key : ∀ a r x : k, ballFn (c * a) (c * r) x = ballFn a r ((c⁻¹ * x + 0 : k) : OnePoint k) := by
    intro a r x
    have h1 : x - c * a = c * (c⁻¹ * x + 0 - a) := by field_simp; ring
    rw [ballFn_coe, ballFn_coe, h1, map_mul, map_mul]
    congr 1
    rw [mul_le_mul_iff_right₀ hv]
  refine hS.1 _ h c⁻¹ 0 (inv_ne_zero hc) _ (by simp [ballFn]) fun x => ?_
  simp only [Pi.add_apply, Pi.smul_apply, key]

theorem ballFn_eq_ballFn_zero {a r : k} (h : valuation k a ≤ valuation k r) : ballFn a r = ballFn 0 r := by
  funext x
  induction x using OnePoint.rec with
  | infty => rfl
  | coe x =>
    rw [ballFn_coe, ballFn_coe, sub_zero]
    congr 1
    refine propext ⟨fun hx => ?_, fun hx => (valuation k).map_sub_le hx h⟩
    have := (valuation k).map_add_le hx h
    rwa [sub_add_cancel] at this

theorem ballFn_congr_radius (a : k) {r s : k} (h : valuation k r = valuation k s) : ballFn a r = ballFn a s := by
  funext x
  induction x using OnePoint.rec with
  | infty => rfl
  | coe x => rw [ballFn_coe, ballFn_coe, h]

theorem Stable.ballFn_mem_and_one_mem_of_sub_mem (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (S : Submodule ℂ (OnePoint k → ℂ)) (hS : Stable S) (ϖ : k)
    (hϖ : valuation k ϖ = uniformizer k) (h : ballFn 0 ϖ - ballFn 1 ϖ ∈ S) :
    ballFn (0 : k) 1 ∈ S ∧ (fun _ => (1 : ℂ)) ∈ S := by
  classical
  have hlt : valuation k ϖ < 1 := hϖ ▸ uniformizer_lt_one
  have hle : ∀ x : k, valuation k x ≤ valuation k ϖ ↔ valuation k x < 1 := fun x => by
    rw [hϖ]; exact le_uniformizer_iff
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    exact uniformizer_ne_zero (hϖ.symm.trans (map_zero _))
  have hdiff : ∀ a : k, valuation k a ≤ 1 → ballFn 0 ϖ - ballFn a ϖ ∈ S := by
    intro a ha
    rcases ha.lt_or_eq with ha | ha
    · rw [ballFn_eq_ballFn_zero ((hle a).2 ha), sub_self]
      exact S.zero_mem
    · have ha0 : a ≠ 0 := by rintro rfl; simp at ha
      have h1 := hS.scale_mem ha0 0 1 (-1) 0 ϖ 1 ϖ (by simpa [sub_eq_add_neg] using h)
      have h2 : valuation k (a * ϖ) = valuation k ϖ := by rw [map_mul, ha, one_mul]
      rw [ballFn_congr_radius _ h2, ballFn_congr_radius _ h2] at h1
      simpa [sub_eq_add_neg] using h1
  obtain ⟨T, hT1, hT2, hT3⟩ := exists_eq_sum_ballFn (r := ϖ) (R := 1) h0 (by simpa using hlt.le)
  simp only [map_one] at hT1 hT2 hT3
  set q : ℂ := (T.card : ℂ) with hqdef
  have hsum : ballFn (0 : k) 1 = ∑ a ∈ T, ballFn a ϖ := by
    rw [hT3 (ballFn 0 1) rfl (fun x hx => by rw [ballFn_coe, if_neg (by simpa using hx)]) (fun x b hb => ?_)]
    · refine Finset.sum_congr rfl fun a ha => ?_
      rw [ballFn_coe, if_pos (by simpa using hT1 a ha), one_smul]
    · have hb1 : valuation k b ≤ 1 := hb.trans hlt.le
      rw [ballFn_coe, ballFn_coe, sub_zero, sub_zero, map_one]
      congr 1
      refine propext ⟨fun hx => ?_, fun hx => (valuation k).map_add_le hx hb1⟩
      have := (valuation k).map_sub_le hx hb1
      rwa [add_sub_cancel_right] at this
  set e : OnePoint k → ℂ := fun _ => 1 with he
  have R1 : (0 : ℂ) • e + (1 : ℂ) • ballFn (0 : k) 1 + (-q) • ballFn (0 : k) ϖ ∈ S := by
    have h1 := S.neg_mem (S.sum_mem fun a (ha : a ∈ T) => hdiff a (hT1 a ha))
    rw [Finset.sum_sub_distrib, ← hsum, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, ← hqdef] at h1
    convert h1 using 1
    module
  have R2 := hS.scale_mem h0 _ _ _ _ _ _ _ R1
  have R3 : (1 - q) • e + q • ballFn (0 : k) 1 + (-1 : ℂ) • ballFn (0 : k) ϖ ∈ S := by
    refine hS.2 _ R1 _ ?_ ?_ fun x hx => ?_
    · simp [ballFn_coe, ballFn, he]; ring
    · simp [ballFn_coe, ballFn, he]
    · have hx0 : 0 < valuation k x := zero_lt_iff.2 (by simpa using hx)
      simp only [Pi.add_apply, Pi.smul_apply, ballFn_coe, sub_zero, map_one, hϖ, le_uniformizer_iff, map_inv₀, he, smul_eq_mul,
        inv_le_one₀ hx0, inv_lt_one₀ hx0]
      rcases lt_trichotomy (valuation k x) 1 with h1 | h1 | h1
      · simp [h1, h1.le, h1.not_ge, h1.not_gt]
      · simp [h1]
      · simp [h1, h1.le, h1.not_ge, h1.not_gt]; ring
  have R4 := hS.scale_mem h0 _ _ _ _ _ _ _ R3
  simp only [mul_zero, mul_one] at R2 R4
  rw [← he] at R2 R4
  have hq1 : (1 - q) ≠ 0 := by
    rw [sub_ne_zero, hqdef]
    exact_mod_cast (hT2 hlt).ne
  have hq2 : (1 + q) ≠ 0 := by
    rw [hqdef]
    exact_mod_cast (by omega : 1 + T.card ≠ 0)
  have h2 : ballFn (0 : k) (ϖ * ϖ) ∈ S := by
    have h3 := S.sub_mem (S.add_mem (S.sub_mem R4 R3) (S.smul_mem q R1)) (S.smul_mem (q + 1 - q ^ 2) R2)
    have h4 : -((1 - q) * (1 - q) * (1 + q)) ≠ 0 := neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hq1 hq1) hq2)
    refine (S.smul_mem_iff h4).1 ?_
    convert h3 using 1
    module
  have hu0 : ballFn (0 : k) 1 ∈ S := hS.ballFn_mem (mul_ne_zero h0 h0) h2 0 one_ne_zero
  have hu1 : ballFn (0 : k) ϖ ∈ S := hS.ballFn_mem (mul_ne_zero h0 h0) h2 0 h0
  refine ⟨hu0, (S.smul_mem_iff hq1).1 ?_⟩
  convert S.add_mem (S.sub_mem R3 (S.smul_mem q hu0)) hu1 using 1
  module

end GlobalTheory.LocGL.ProjLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BallFnSubMemOfRadial
section
open ValuativeRel OnePoint GlobalTheory.LocGL.ProjLine

namespace GlobalTheory.LocGL.ProjLine

theorem exists_jump_point {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (f : k → ℂ) {r : k} (hr : r ≠ 0) (h : ∀ x, valuation k x ≤ valuation k r → f x = f 0) {y : k} (hy : f y ≠ f 0) :
    ∃ b : k, f b ≠ f 0 ∧ ∀ x, valuation k x < valuation k b → f x = f 0 := by
  classical
  have hπ : (0 : ValueGroupWithZero k) < uniformizer k := uniformizer_pos
  have hr' : 0 < valuation k r := zero_lt_iff.2 (by simpa using hr)
  have hex : ∃ n : ℕ, ∃ x, valuation k x * uniformizer k ^ n ≤ valuation k r ∧ f x ≠ f 0 := by
    have hy0 : 0 < valuation k y := zero_lt_iff.2 (by rintro h0; rw [map_eq_zero] at h0; exact hy (by rw [h0]))
    obtain ⟨n, hn⟩ := exists_pow_lt₀ (uniformizer_lt_one (R := k))
      (Units.mk0 (valuation k r / valuation k y) (div_pos hr' hy0).ne')
    refine ⟨n, y, ?_, hy⟩
    rw [Units.val_mk0, lt_div_iff₀ hy0, mul_comm] at hn
    exact hn.le
  obtain ⟨b, hb, hb'⟩ := Nat.find_spec hex
  refine ⟨b, hb', fun x hx => ?_⟩
  by_contra hne
  rcases hm : Nat.find hex with _ | m
  · rw [hm, pow_zero, mul_one] at hb
    exact hb' (h b hb)
  · refine Nat.find_min hex (m := m) (by omega) ⟨x, ?_, hne⟩
    rw [hm] at hb
    have hb0 : 0 < valuation k b := zero_le'.trans_lt hx
    have h1 : valuation k x / valuation k b ≤ uniformizer k := le_uniformizer_iff.2 ((div_lt_one₀ hb0).2 hx)
    rw [div_le_iff₀ hb0] at h1
    calc valuation k x * uniformizer k ^ m ≤ uniformizer k * valuation k b * uniformizer k ^ m := by gcongr
      _ = valuation k b * uniformizer k ^ (m + 1) := by rw [pow_succ]; ac_rfl
      _ ≤ _ := hb

theorem ballFn_sub_mem_of_radial (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (S : Submodule ℂ (OnePoint k → ℂ)) (hS : Stable S) (F : OnePoint k → ℂ) (hF : F ∈ S)
    (hrad : ∀ u x : k, valuation k u = 1 → F ((u * x : k) : OnePoint k) = F (x : OnePoint k))
    (h0 : ∃ r : k, r ≠ 0 ∧ ∀ x : k, valuation k x ≤ valuation k r → F (x : OnePoint k) = F ((0 : k) : OnePoint k))
    (hi : ∃ R : k, ∀ x : k, valuation k R < valuation k x → F (x : OnePoint k) = F ∞)
    (hne : F ((0 : k) : OnePoint k) ≠ F ∞) (ϖ : k) (hϖ : valuation k ϖ = uniformizer k) :
    ballFn 0 ϖ - ballFn 1 ϖ ∈ S := by
  classical
  obtain ⟨r, hr, h0⟩ := h0
  obtain ⟨R, hi⟩ := hi
  have hπ : (0 : ValueGroupWithZero k) < uniformizer k := uniformizer_pos
  have hy : ∃ y : k, valuation k R < valuation k y := by
    by_cases hR : R = 0
    · exact ⟨1, by simp [hR]⟩
    · have hR' : 0 < valuation k R := zero_lt_iff.2 (by simpa using hR)
      refine ⟨R / ϖ, ?_⟩
      rw [map_div₀, hϖ, lt_div_iff₀ hπ]
      exact mul_lt_of_lt_one_right hR' uniformizer_lt_one
  obtain ⟨y, hy⟩ := hy
  obtain ⟨b, hb, hb'⟩ := exists_jump_point (fun x : k => F x) hr h0 (y := y) (by
    show F y ≠ F (0 : k)
    rw [hi y hy]; exact hne.symm)
  have hb0 : b ≠ 0 := by rintro rfl; exact hb rfl
  have hvb : 0 < valuation k b := zero_lt_iff.2 (by simpa using hb0)
  let g : k → ℂ := fun x => F ((b * x : k) : OnePoint k)
  have g1 : ∀ x, valuation k x < 1 → g x = F (0 : k) := fun x hx => hb' _ (by
    rw [map_mul]; exact mul_lt_of_lt_one_right hvb hx)
  have g2 : ∀ x, valuation k x = 1 → g x = F b := fun x hx => by
    show F ((b * x : k) : OnePoint k) = _
    rw [mul_comm]; exact hrad x b hx
  have g3 : ∀ x z, x ≠ 0 → valuation k z = valuation k x → g z = g x := fun x z hx hz => by
    have hvx : valuation k x ≠ 0 := by simpa using hx
    have := hrad (z / x) (b * x) (by rw [map_div₀, hz, div_self hvx])
    show F ((b * z : k) : OnePoint k) = F ((b * x : k) : OnePoint k)
    rw [← this]; congr 2; field_simp
  have hG : (fun x : OnePoint k => x.elim (F ∞) g) ∈ S :=
    hS.1 F hF b 0 hb0 _ rfl fun x => by rw [add_zero]; rfl
  have hG' : (fun x : OnePoint k => x.elim (F ∞) fun x => g (x - 1)) ∈ S :=
    hS.1 F hF b (-b) hb0 _ rfl fun x => by
      show F ((b * (x - 1) : k) : OnePoint k) = _
      congr 2; ring
  have hc : F (0 : k) - F b ≠ 0 := sub_ne_zero.2 hb.symm
  rw [← S.smul_mem_iff hc]
  convert S.sub_mem hG hG' using 1
  funext x
  induction x using OnePoint.rec with
  | infty => simp [ballFn]
  | coe x =>
    show (F (0 : k) - F b) * (ballFn 0 ϖ x - ballFn 1 ϖ x) = g x - g (x - 1)
    rw [ballFn_coe, ballFn_coe, hϖ, sub_zero]
    simp only [le_uniformizer_iff]
    by_cases h1 : valuation k x < 1
    · have h2 : valuation k (x - 1) = 1 := by
        rw [Valuation.map_sub_swap]; exact (valuation k).map_one_sub_of_lt h1
      rw [if_pos h1, if_neg (by rw [h2]; exact lt_irrefl _), g1 x h1, g2 _ h2]; ring
    · by_cases h2 : valuation k (x - 1) < 1
      · have h3 : valuation k x = 1 := by
          have := (valuation k).map_one_add_of_lt h2
          rwa [add_sub_cancel] at this
        rw [if_neg h1, if_pos h2, g1 _ h2, g2 _ h3]; ring
      · have hx0 : x ≠ 0 := by rintro rfl; exact h1 (by simp)
        have h3 : valuation k (x - 1) = valuation k x := by
          rcases (not_lt.1 h1).eq_or_lt with h4 | h4
          · refine le_antisymm ?_ (h4 ▸ not_lt.1 h2)
            exact (valuation k).map_sub_le le_rfl (by rw [map_one]; exact h4.le)
          · exact (valuation k).map_sub_eq_of_lt_left (by rwa [map_one])
        rw [if_neg h1, if_neg h2, g3 x _ hx0 h3]; ring

end GlobalTheory.LocGL.ProjLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoHypothesisGlobalStepAtQd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.BKAtQD

theorem admBK_embeddingTypeJumps : ∀ (D : D7), EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.LiteratureHypotheses (D := D) →
    ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.admBK i := by
  intro D hBK hLit i hi w hw C
  obtain ⟨-, hTD, -⟩ := hLit i hi
  exact ⟨(hTD w hw C).1, (hTD w hw C).2,
    fun _ => TruncatedSeriesCountingIdentities.bkBAt_of_core _ _ _ (hBK _ _).2.2.2.1 (GlobalTheory.AdmBK.litGoodO_all _ _)⟩

end GlobalTheory.BKAtQD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousLagTerm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open Filter
open scoped TensorProduct InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift.TermCont

open GlobalTheory.RawLift

theorem continuous_lagTerm : ∀ D : D7, ∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr,
    SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ →
      ∀ Y : Lag W, Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ →
        Continuous fun g : GA D W => lagTerm μ 𝓕 (fr Y) (om (1, g) f₁) f₂ := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ f₂ h₁ h₂ Y _
  have hw := hS.weil
  have hψ := hw.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ h₂
  have hJ := GlobalTheory.ThetaJointCont.continuous_om_oriented hw h₁
  have hrm : ∀ (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E), Continuous fun u : WO V W => ratMul C u := fun C => by
    unfold ratMul
    exact continuous_const.matrix_mul continuous_id
  have hμ1 : μ 𝓕 = 1 := hS.covol.2.2
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [hμ1]; exact ENNReal.one_ne_top)
  have : SecondCountableTopology (GA D W) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W).2.1
  refine continuous_iff_continuousAt.2 fun g₀ => ?_

  have hc0 : Continuous fun w : WO V W => om ((1 : GA D V), g₀) f₁ w :=
    hJ.comp (continuous_const.prodMk continuous_id)
  obtain ⟨κ, hκ⟩ := hK.exists_bound_of_continuousOn hc0.continuousOn
  have hev : ∀ᶠ g in 𝓝 g₀, ∀ w ∈ K, ‖om ((1 : GA D V), g) f₁ w‖ ≤ κ + 1 := by
    refine hK.eventually_forall_of_forall_eventually fun w hw' => ?_
    have hc : Continuous fun y : GA D W × WO V W => ‖om ((1 : GA D V), y.1) f₁ y.2‖ :=
      (hJ.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)).norm
    exact (hc.continuousAt.eventually_lt continuousAt_const ((hκ w hw').trans_lt (lt_add_one κ))).mono
      fun y hy => hy.le
  have hall : ∀ᶠ g in 𝓝 g₀, ∀ w, ‖om ((1 : GA D V), g) f₁ w‖ ≤ κ + 1 := hev.mono fun g hg w => by
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← GlobalTheory.OrientedHeis.theta_norm_periodic hψ (hw.om_pres _ f₁ h₁) γ hγ w]
    exact hg _ h
  unfold lagTerm
  refine continuousAt_of_dominated (bound := fun _ => (κ + 1) * C₂) ?_ ?_ (integrable_const _) ?_
  · refine Eventually.of_forall fun g => ?_
    exact ((((hw.om_pres _ f₁ h₁).cont.comp (hrm _)).mul
      (continuous_star.comp (h₂.cont.comp (hrm _))))).aestronglyMeasurable
  · refine hall.mono fun g hg => Eventually.of_forall fun u => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (hg _) (hC₂ _) (norm_nonneg _) ((norm_nonneg _).trans (hg 0))
  · refine Eventually.of_forall fun u => ?_
    exact ((hw.om_cont f₁ h₁ _).comp (continuous_const.prodMk continuous_id)).continuousAt.mul continuousAt_const

end GlobalTheory.RawLift.TermCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ElementDenominatorAdm7
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem elementDenominator_adm7 : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm7 D := by
  intro D l _ _ K LL _ T _
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  exact @_root_.GlobalTheory.H1fGeneration.h1fGen_tied l _ (D.loc l) (D.locA l) (D.locT l) K LL (Fintype.ofFinite _) T _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComparisonMatrixPrismCoproductStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_comparison_matrix_prismCoproduct : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → (∀ g, IsUnit (ρ g)) → ∀ (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)), ∃ ε : Matrix (Fin d) (Fin d) En.Q.A, ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) := by
  first | exact @GlobalTheory.BSP.Height.exists_rel_env | exact GlobalTheory.BSP.Height.exists_rel_env | (intros; apply GlobalTheory.BSP.Height.exists_rel_env <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFrameLimitLatticeBreuilKisinTowerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deRhamFrame_limitLattice_breuilKisinTower : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val), (∀ n, (F n).IsDR) → ∃ F₀ : Frame bk N d (fun g => (ρ g).val), F₀.IsDR ∧ ((∀ n, (F n).IsCr) → F₀.IsCr) ∧ ∃ r, ∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r := by
  first | (exact @GlobalTheory.BKLim.limit_frame_exists) | (exact GlobalTheory.BKLim.limit_frame_exists) | (intros; apply GlobalTheory.BKLim.limit_frame_exists  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleQuotientFinitelyGeneratedRep
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.IrrQuot

theorem main : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (s : Finset V), Nontrivial V → Submodule.span ℂ {w | ∃ g : G, ∃ v ∈ s, w = ρ g v} = ⊤ → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ G W), τ.IsIrreducible ∧ ∃ f : ρ.IntertwiningMap τ, Function.Surjective f := by
  intro G V _ _ _ ρ s hV hspan
  have key : ∀ T : Subrepresentation ρ, (∀ v ∈ s, v ∈ T.toSubmodule) → T = ⊤ := by
    intro T hT
    apply Subrepresentation.toSubmodule_injective
    refine eq_top_iff.2 ?_
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro w ⟨g, v, hv, rfl⟩
    exact T.apply_mem_toSubmodule g (hT v hv)
  haveI : Module.Finite (MonoidAlgebra ℂ G) ρ.asModule := by
    let t : Finset ρ.asModule := s
    refine ⟨⟨t, ?_⟩⟩
    have h := key (Subrepresentation.ofSubmodule' (Submodule.span (MonoidAlgebra ℂ G) (t : Set ρ.asModule)))
      (fun v hv => Submodule.subset_span (R := MonoidAlgebra ℂ G) (s := (t : Set ρ.asModule)) hv)
    refine eq_top_iff.2 fun x _ => ?_
    have hx : x ∈ Subrepresentation.ofSubmodule' (Submodule.span (MonoidAlgebra ℂ G) (t : Set ρ.asModule)) := by
      rw [h]; trivial
    exact hx
  haveI : IsCoatomic (Subrepresentation ρ) :=
    (OrderIso.isCoatomic_iff Subrepresentation.subrepresentationSubmoduleOrderIso).2 inferInstance
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := trivial
    rw [← h] at this
    exact hv this
  obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  refine ⟨_, inferInstance, inferInstance, GlobalTheory.SmGL.subQuot ⊤ M, GlobalTheory.SmGL.isIrreducible_subQuot hM.covBy_top, ?_⟩
  refine ⟨⟨(Submodule.mkQ _).comp (LinearMap.codRestrict (⊤ : Subrepresentation ρ).toSubmodule LinearMap.id (fun _ => trivial)), fun g => rfl⟩, ?_⟩
  intro y
  obtain ⟨⟨v, _⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨v, rfl⟩

end GlobalTheory.IrrQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPairingDstDcrisFrobeniusFixedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pairing_Dst_Dcris_frobenius_fixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → ∃ B : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) →ₗ[ℚ_[l]] ℚ_[l], (∀ x ∈ Dst P ρ, ∀ w, B (monV P ℚ_[l] V x) w = 0) ∧ (∀ x ∈ Dst P ρ, ∀ w, B ((l : ℚ_[l]) • phiV P ℚ_[l] V x) w = B x w) ∧ ∀ w, (∀ x ∈ Dst P ρ, B x w = 0) → w = 0 := by
  first | exact @GlobalTheory.PMon.exists_pairing_Dst_Dcris_phi_one | exact GlobalTheory.PMon.exists_pairing_Dst_Dcris_phi_one | (intros; apply GlobalTheory.PMon.exists_pairing_Dst_Dcris_phi_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fClassFromWachPairStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H1f_class_of_wach_pair : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → W.GKs = ⊤ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := by
  first | exact @GlobalTheory.NL.ExtClassKs.main | exact GlobalTheory.NL.ExtClassKs.main | (intros; apply GlobalTheory.NL.ExtClassKs.main <;> assumption)
end

