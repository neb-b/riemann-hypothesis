module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0045
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarCapelliTruncatedPerelomovPopov
public import GroundTheory.PAdicHodge.AInfGalois
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandInvariantsCentralCharacter
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace GlobalTheory.GelfandOfCapelli

open Finset Polynomial
open GlobalTheory.Dec (gelfVal)

theorem main_succ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (F : Fin (m+1) → Fin (m+1) → A)
    (χ : Fin (m+1) → ℂ) (hF : GlRel F)
    (hq : ∀ w : ℂ, qdet F w = algebraMap ℂ A ((GlobalTheory.CapelliNewton.capQ m χ).eval w)) (N : ℕ) :
    etr F N = algebraMap ℂ A (gelfVal χ N) := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
  set Q := GlobalTheory.CapelliNewton.capQ m χ with hQ
  have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → A, ∀ w : ℂ,
      qminor F (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
    intro i j
    obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap A (m + 1) m F (Fin.succAbove j) (Fin.succAbove i) 0
    exact ⟨c', fun w => by simpa using hc' w⟩
  choose cm hcm using hmin
  let Rc : ℕ → A := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * cm i j d * epow F (N + 1) j i
  have hR : ∀ w : ℂ, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) *
      qminor F (Fin.succAbove j) (Fin.succAbove i) w * epow F (N + 1) j i
      = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
    intro w
    simp only [Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
    conv_lhs => enter [2, x]; rw [sum_comm]
    rw [sum_comm]
  let Rp : ℂ[X] := ∑ d ∈ range (m + 1), C (φ (Rc d)) * X ^ d
  have hRp : ∀ w : ℂ, φ (∑ d ∈ range (m + 1), w ^ d • Rc d) = Rp.eval w := by
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Rp, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, map_sum, map_smul, smul_eq_mul]
    exact sum_congr rfl fun d _ => mul_comm _ _
  have hRpdeg : Rp.natDegree ≤ m := natDegree_sum_le_of_forall_le _ _ fun i hi =>
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (mem_range.mp hi))
  have hφa : ∀ c : ℂ, φ (algebraMap ℂ A c) = c * φ 1 := fun c => by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
  have hrec : ∀ w : ℂ, (w - m) ^ (N + 1) * (Q.eval (w + 1) - Q.eval w) * φ 1 + (-1) ^ N * Rp.eval w
      = Q.eval w * ∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * φ (etr F k) := by
    intro w
    have h1 := congrArg φ (_root_.GlobalTheory.TracedComatrix.traced_comatrix A m F hF w N)
    rw [← _root_.GlobalTheory.qdet_add_one_sub_eq_sum_qminor, hR] at h1
    simp only [hq, ← Algebra.smul_def, map_add (f := _), map_smul, smul_eq_mul, hRp] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mul_sum, map_sum, map_smul, map_sub, smul_eq_mul, hφa] at h1
    rw [mul_sum]
    linear_combination h1
  obtain ⟨rs, hrs, hrsE⟩ := _root_.GlobalTheory.ScalarNewton.scalar_newton m N χ
  let S : ℂ[X] := ∑ k ∈ range (N + 1),
    C ((-1) ^ k * (φ (etr F k) - gelfVal χ k * φ 1)) * (X - C (m : ℂ)) ^ (N - k)
  have hSe : ∀ w : ℂ, S.eval w = (∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * φ (etr F k))
      - φ 1 * ∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * gelfVal χ k := by
    intro w
    simp only [S, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  have hQS : Q * S = C ((-1) ^ N) * Rp + C (φ 1) * rs := by
    refine Polynomial.funext fun w => ?_
    have h2 := hrsE w
    rw [← GlobalTheory.CapelliNewton.capQ_eval m χ (w + 1), ← GlobalTheory.CapelliNewton.capQ_eval m χ w, ← hQ] at h2
    simp only [eval_mul, eval_add, eval_C, hSe]
    linear_combination -hrec w + φ 1 * h2
  have hS0 : S = 0 := by
    by_contra hne
    have hd := (GlobalTheory.CapelliNewton.capQ_monic m χ).natDegree_mul' hne
    rw [← hQ, hQS, GlobalTheory.CapelliNewton.capQ_natDegree] at hd
    have hle : (C ((-1 : ℂ) ^ N) * Rp + C (φ 1) * rs).natDegree ≤ m :=
      (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hRpdeg)
        ((natDegree_C_mul_le _ _).trans hrs))
    omega
  have h0 := congrArg (eval (m : ℂ)) hS0
  simp only [S, eval_zero, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self] at h0
  rw [sum_eq_single N (fun b hb hbN => by
      rw [zero_pow (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.mp (mem_range.mp hb)) hbN)), mul_zero])
    (fun h => absurd (self_mem_range_succ N) h)] at h0
  rw [Nat.sub_self, pow_zero, mul_one] at h0
  have hne : ((-1 : ℂ)) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [map_sub, hφa]
  exact mul_left_cancel₀ hne (by linear_combination h0)

theorem gelfand_of_capelli : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (F : Fin n → Fin n → A) (χ : Fin n → ℂ),
    GlRel F → (∀ u : ℂ, qdet F (u + ((n : ℂ) - 1) / 2) = algebraMap ℂ A (∏ s, (u + χ s))) →
    ∀ k : ℕ, etr F (k + 1) = algebraMap ℂ A (GlobalTheory.Dec.gelfVal χ (k + 1)) := by
  intro A _ _ n F χ hF hq k
  cases n with
  | zero => simp [etr, gelfVal]
  | succ m =>
    refine main_succ A m F χ hF (fun w => ?_) (k + 1)
    calc qdet F w = qdet F ((w - (m : ℂ) / 2) + (((m + 1 : ℕ) : ℂ) - 1) / 2) := by congr 1; push_cast; ring
      _ = algebraMap ℂ A (∏ s, ((w - (m : ℂ) / 2) + χ s)) := hq _
      _ = _ := by rw [GlobalTheory.CapelliNewton.capQ_eval]

end GlobalTheory.GelfandOfCapelli
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandInvariantsDetermineMultiset
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace GlobalTheory.GelfandInj

open Finset Polynomial

theorem capQ_eq_prod (m : ℕ) (χ : Fin (m+1) → ℂ) :
    GlobalTheory.CapelliNewton.capQ m χ
      = (((Multiset.map χ Finset.univ.val).map (fun a => ((m : ℂ) / 2 - a))).map (fun a => X - C a)).prod := by
  unfold GlobalTheory.CapelliNewton.capQ
  rw [Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun s _ => ?_
  simp only [Function.comp_apply, map_sub]
  ring

theorem capQ_roots (m : ℕ) (χ : Fin (m+1) → ℂ) :
    (GlobalTheory.CapelliNewton.capQ m χ).roots = (Multiset.map χ Finset.univ.val).map (fun a => ((m : ℂ) / 2 - a)) := by
  rw [capQ_eq_prod, Polynomial.roots_multiset_prod_X_sub_C]

theorem gelfVal_multiset_eq : ∀ (n : ℕ) (χ χ' : Fin n → ℂ), (∀ k : ℕ, GlobalTheory.Dec.gelfVal χ (k + 1) = GlobalTheory.Dec.gelfVal χ' (k + 1)) → Multiset.map χ Finset.univ.val = Multiset.map χ' Finset.univ.val := by
  intro n χ χ' h
  cases n with
  | zero => simp
  | succ m =>
    have hall : ∀ k, GlobalTheory.Dec.gelfVal χ k = GlobalTheory.Dec.gelfVal χ' k := by
      intro k
      cases k with
      | zero => rw [GlobalTheory.CapelliNewton.gelfVal_zero, GlobalTheory.CapelliNewton.gelfVal_zero]
      | succ k => exact h k
    have hgv : GlobalTheory.Dec.gelfVal χ = GlobalTheory.Dec.gelfVal χ' := funext hall
    obtain ⟨r, hr, hrE⟩ := _root_.GlobalTheory.ScalarNewton.scalar_newton m (m + 1) χ
    obtain ⟨r', hr', hrE'⟩ := _root_.GlobalTheory.ScalarNewton.scalar_newton m (m + 1) χ'
    have hf := _root_.GlobalTheory.newton_recursion_poly_unique m (m + 1) (GlobalTheory.Dec.gelfVal χ)
      (GlobalTheory.CapelliNewton.capQ m χ - GlobalTheory.CapelliNewton.capQ m χ') (r - r')
      (Nat.lt_succ_self m) (GlobalTheory.CapelliNewton.gelfVal_zero m χ) ?_ ?_ ?_
    · have hQ : GlobalTheory.CapelliNewton.capQ m χ = GlobalTheory.CapelliNewton.capQ m χ' := sub_eq_zero.mp hf
      have hroots := congrArg Polynomial.roots hQ
      rw [capQ_roots, capQ_roots] at hroots
      exact Multiset.map_injective (fun a b hab => by simpa using hab) hroots
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [coeff_sub]
      rcases Nat.lt_or_ge (m + 1) k with hlt | hge
      · rw [coeff_eq_zero_of_natDegree_lt (by rw [GlobalTheory.CapelliNewton.capQ_natDegree]; exact hlt),
          coeff_eq_zero_of_natDegree_lt (by rw [GlobalTheory.CapelliNewton.capQ_natDegree]; exact hlt), sub_zero]
      · have hk' : k = m + 1 := le_antisymm hge hk
        subst hk'
        have h1 := (GlobalTheory.CapelliNewton.capQ_monic m χ).coeff_natDegree
        have h2 := (GlobalTheory.CapelliNewton.capQ_monic m χ').coeff_natDegree
        rw [GlobalTheory.CapelliNewton.capQ_natDegree] at h1 h2
        rw [h1, h2, sub_self]
    · exact (natDegree_sub_le _ _).trans (max_le hr hr')
    · intro u
      have h1 := hrE u
      have h2 := hrE' u
      rw [← hgv] at h2
      rw [← GlobalTheory.CapelliNewton.capQ_eval m χ (u + 1), ← GlobalTheory.CapelliNewton.capQ_eval m χ u] at h1
      rw [← GlobalTheory.CapelliNewton.capQ_eval m χ' (u + 1), ← GlobalTheory.CapelliNewton.capQ_eval m χ' u] at h2
      simp only [eval_sub]
      linear_combination h1 - h2

end GlobalTheory.GelfandInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasEqChartMeasOfCompatOn
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

theorem glueMeas_eq_chartMeas_of_compat_on : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {ρ : κ → Y → ENNReal} (e' : OpenPartialHomeomorph Y (V n)) (ρ' : Y → ENNReal), S ⊆ e'.source → (∀ j, DifferentiableOn ℂ (e j ∘ e'.symm) (e'.target ∩ e'.symm ⁻¹' (e j).source)) → (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source → ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y) → (∀ j y, y ∈ S → y ∈ (e j).source → ρ' y = ENNReal.ofReal (‖transDet e' (e j) y‖ ^ 2) * ρ j y) → glueMeas e ρ S = chartMeas e' ρ' S := by
  intro n Y κ _ _ _ _ e hd hcov S hS ρ e' ρ' hSe hd' hρ hρ'
  have hm := GlobalTheory.ChernScale.glueMeas_restrict_eq e (ρ := ρ) (ρ' := fun i => S.indicator (ρ i)) (c := 1)
    ENNReal.one_ne_top hS (fun i y _ hy => by rw [one_mul, Set.indicator_of_mem hy])
  rw [one_smul] at hm
  have cσ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      S.indicator (ρ i) y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * S.indicator (ρ j) y := by
    intro i j y hi hj
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; exact hρ i j y hy hi hj
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  have key : (glueMeas e ρ).restrict S = (chartMeas e' ρ').restrict S := by
    rw [hm]
    refine ext_of_cover (fun i => (e i).source) (fun i => (e i).open_source) hcov fun i A hA hAi => ?_
    have hsub : A ∩ S ⊆ (e i).source := Set.inter_subset_left.trans hAi
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA,
      glueMeas_apply e (fun i => S.indicator (ρ i)) hd cσ i (hA.inter hS) hsub]
    refine (chartMeas_eq e' (e i) (hd' i) (hA.inter hS) (Set.inter_subset_right.trans hSe) hsub
      fun y hy => ?_).symm
    rw [Set.indicator_of_mem hy.2]
    exact hρ' i y hy.2 (hsub hy)
  have := congrArg (fun μ : Measure Y => μ S) key
  simpa only [Measure.restrict_apply_self] using this

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupAverageComponentwiseSubgroupEqProd
section
open Filter GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.AvgRestr

private lemma mem_rStab_iff_forall_mul_right_invariant {H : Type} [Group H] (u : H → ℂ) (k : H) :
    k ∈ rStab u ↔ ∀ x, u (x * k) = u x := Iff.rfl

private lemma avg_eq_inv_index_mul_finsum_rStab_quotient {H : Type} [Group H] (u : H → ℂ) :
    avg u = ((rStab u).index : ℂ)⁻¹ * ∑ᶠ q : H ⧸ rStab u, u q.out := rfl

lemma apply_out {H : Type} [Group H] (u : H → ℂ) (x : H) : u ((x : H ⧸ rStab u).out) = u x := by
  have h : ((x : H ⧸ rStab u).out)⁻¹ * x ∈ rStab u :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (x : H ⧸ rStab u))
  have h2 := (mem_rStab_iff_forall_mul_right_invariant u _).mp h ((x : H ⧸ rStab u).out)
  rw [mul_inv_cancel_left] at h2
  exact h2.symm

private lemma rStab_comp_eq_comap_of_surjective {A B : Type} [Group A] [Group B] (π : A →* B)
    (hπ : Function.Surjective π) (v : B → ℂ) : rStab (v ∘ π) = (rStab v).comap π := by
  ext k
  rw [Subgroup.mem_comap, mem_rStab_iff_forall_mul_right_invariant, mem_rStab_iff_forall_mul_right_invariant]
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := hπ y
    have h2 := h x
    simpa [Function.comp, map_mul] using h2
  · intro h x
    simp only [Function.comp_apply, map_mul]
    exact h (π x)

private lemma bijective_quotient_comap_of_surjective {A B : Type} [Group A] [Group B] (π : A →* B)
    (hπ : Function.Surjective π) (S : Subgroup B) :
    Function.Bijective (fun q : A ⧸ S.comap π => ((π q.out : B) : B ⧸ S)) := by
  constructor
  · intro q q' h
    have h2 := QuotientGroup.eq.mp h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_comap,
      map_mul, map_inv]
    exact h2
  · intro z
    obtain ⟨a, ha⟩ := hπ z.out
    refine ⟨(a : A ⧸ S.comap π), ?_⟩
    have h2 := QuotientGroup.eq.mp (QuotientGroup.out_eq' (a : A ⧸ S.comap π))
    rw [Subgroup.mem_comap, map_mul, map_inv] at h2
    show ((π (a : A ⧸ S.comap π).out : B) : B ⧸ S) = z
    rw [← QuotientGroup.out_eq' z, ← ha, QuotientGroup.eq]
    exact h2

theorem avg_comp_surj {A B : Type} [Group A] [Group B] (π : A →* B) (hπ : Function.Surjective π) (v : B → ℂ) :
    avg (v ∘ π) = avg v := by
  rw [avg_eq_inv_index_mul_finsum_rStab_quotient, avg_eq_inv_index_mul_finsum_rStab_quotient, rStab_comp_eq_comap_of_surjective π hπ v]
  let e := Equiv.ofBijective _ (bijective_quotient_comap_of_surjective π hπ (rStab v))
  have hidx : ((rStab v).comap π).index = (rStab v).index := by
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
    exact Nat.card_congr e
  rw [hidx]
  congr 1
  refine (finsum_congr ?_).trans (finsum_comp_equiv e (f := fun z : B ⧸ rStab v => v z.out))
  intro q
  exact (apply_out v (π q.out)).symm

private lemma bijective_pi_quotient_to_quotient_pi {J : Type} (M : J → Type) [∀ j, Group (M j)] (R : ∀ j, Subgroup (M j)) :
    Function.Bijective
      (fun q : (∀ j, M j) ⧸ Subgroup.pi Set.univ R => fun j => ((q.out j : M j) : M j ⧸ R j)) := by
  constructor
  · intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_pi]
    intro j _
    have h2 := QuotientGroup.eq.mp (congrFun h j)
    simpa only [Pi.mul_apply, Pi.inv_apply] using h2
  · intro z
    refine ⟨(((fun j => (z j).out) : ∀ j, M j) : (∀ j, M j) ⧸ Subgroup.pi Set.univ R), ?_⟩
    funext j
    have hm := QuotientGroup.eq.mp
      (QuotientGroup.out_eq' ((((fun j => (z j).out) : ∀ j, M j)) : (∀ j, M j) ⧸ Subgroup.pi Set.univ R))
    have hj := (Subgroup.mem_pi _).mp hm j (Set.mem_univ j)
    simp only [Pi.mul_apply, Pi.inv_apply] at hj
    show ((_ : M j) : M j ⧸ R j) = z j
    rw [← QuotientGroup.out_eq' (z j), QuotientGroup.eq]
    exact hj

theorem avg_pi {J : Type} [Fintype J] (M : J → Type) [∀ j, Group (M j)] (v : ∀ j, M j → ℂ)
    (hv : ∀ j, (rStab (v j)).index ≠ 0) :
    avg (fun x : (∀ j, M j) => ∏ j, v j (x j)) = ∏ j, avg (v j) := by
  classical
  haveI : ∀ j, (rStab (v j)).FiniteIndex := fun j => ⟨hv j⟩
  haveI : ∀ j, Fintype (M j ⧸ rStab (v j)) := fun j => Fintype.ofFinite _
  let S : Subgroup (∀ j, M j) := Subgroup.pi Set.univ (fun j => rStab (v j))
  have hS : S ≤ rStab (fun x : (∀ j, M j) => ∏ j, v j (x j)) := by
    intro k hk
    rw [mem_rStab_iff_forall_mul_right_invariant]
    intro x
    refine Finset.prod_congr rfl (fun j _ => ?_)
    exact (mem_rStab_iff_forall_mul_right_invariant (v j) (k j)).mp ((Subgroup.mem_pi _).mp hk j (Set.mem_univ j)) (x j)
  let e := Equiv.ofBijective _ (bijective_pi_quotient_to_quotient_pi M (fun j => rStab (v j)))
  have hidx : S.index = ∏ j, (rStab (v j)).index := by
    rw [Subgroup.index_eq_card, Nat.card_congr e, Nat.card_pi]
    simp only [Subgroup.index_eq_card]
  have hS0 : S.index ≠ 0 := by
    rw [hidx]; exact Finset.prod_ne_zero_iff.mpr (fun j _ => hv j)
  have hsum : (∑ᶠ q : (∀ j, M j) ⧸ S, ∏ j, v j (q.out j)) = ∏ j, ∑ᶠ q : M j ⧸ rStab (v j), v j q.out := by
    have h1 : ∀ q : (∀ j, M j) ⧸ S, ∏ j, v j (q.out j) = ∏ j, v j ((e q j).out) := by
      intro q
      refine Finset.prod_congr rfl (fun j _ => ?_)
      exact (apply_out (v j) (q.out j)).symm
    rw [finsum_congr h1]
    refine (finsum_comp_equiv e (f := fun z : (∀ j, M j ⧸ rStab (v j)) => ∏ j, v j (z j).out)).trans ?_
    rw [finsum_eq_sum_of_fintype]
    simp only [finsum_eq_sum_of_fintype]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [GlobalTheory.BCT.avg_eq_of_le_rStab _ _ S hS hS0]
  simp only [avg_eq_inv_index_mul_finsum_rStab_quotient]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← Nat.cast_prod, ← hidx, hsum]

theorem avg_restrProd : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (K : Subgroup G) (KH : ∀ i, Subgroup (H i)) (hK : ∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) (u : ∀ i, KH i → ℂ), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ i, (rStab (u i)).index ≠ 0) → (∀ᶠ i in cofinite, ∀ k, u i k = 1) → avg (fun k : K => ∏ᶠ i, u i ⟨p i k, (hK k).1 k.2 i⟩) = ∏ᶠ i, avg (u i) := by
  intro ι G _ H _ p K KH hK u happ hu h1
  classical
  have hs := Filter.eventually_cofinite.mp h1
  let T := hs.toFinset
  let π : K →* ∀ j : T, KH j :=
    MonoidHom.pi (fun j : T => ((p j).comp K.subtype).codRestrict (KH j) (fun k => (hK k).1 k.2 j))
  have hπ : Function.Surjective π := by
    intro y
    let y' : ∀ i, H i := fun i => if h : i ∈ T then ((y ⟨i, h⟩ : KH i) : H i) else 1
    have hy' : ∀ i, y' i ∈ KH i := by
      intro i
      simp only [y']
      split_ifs with h
      · exact (y ⟨i, h⟩).2
      · exact (KH i).one_mem
    obtain ⟨x, hx⟩ := happ y' (Filter.Eventually.of_forall hy')
    have hxK : x ∈ K := (hK x).2 (fun i => by rw [hx i]; exact hy' i)
    refine ⟨⟨x, hxK⟩, ?_⟩
    funext j
    apply Subtype.ext
    change p (j : ι) x = ((y j : KH (j : ι)) : H (j : ι))
    rw [hx]
    simp [y', j.2]
  have hfun : (fun k : K => ∏ᶠ i, u i ⟨p i k, (hK k).1 k.2 i⟩) =
      (fun y : (∀ j : T, KH j) => ∏ j : T, u j (y j)) ∘ π := by
    funext k
    rw [Function.comp_apply, finprod_eq_prod_of_mulSupport_subset _ (s := T)]
    · exact (Finset.prod_coe_sort T (fun i => u i ⟨p i k, (hK k).1 k.2 i⟩)).symm
    · intro i hi
      simp only [Finset.mem_coe, T, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      intro hall
      exact (Function.mem_mulSupport.mp hi) (hall _)
  rw [hfun, avg_comp_surj π hπ]
  refine (avg_pi (fun j : T => (KH j : Type)) (fun j => u j) (fun j => hu j)).trans ?_
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T)]
  · exact Finset.prod_coe_sort T (fun i => avg (u i))
  · intro i hi
    simp only [Finset.mem_coe, T, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    intro hall
    apply Function.mem_mulSupport.mp hi
    have hc : u i = fun _ => 1 := funext hall
    rw [hc]
    exact (GlobalTheory.AvgLin.avg_linear_translate_const _ (u i) (u i) 1 1 (hu i) (hu i)).2.2.2

end GlobalTheory.AvgRestr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfIsCompAlongSplit
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitSatake

theorem hasSatGL_of_isCompAlong_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ₁ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ρ₂ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W),
    IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) ρ₁ →
    IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) ρ₂ →
    ∀ T : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w ρ₁ T → GlobalTheory.LFun.HasSatGL w ρ₂ T := by
  intro E _ _ _ n π hπ w hw V W _ _ _ _ ρ₁ ρ₂ h₁ h₂ T hT
  obtain ⟨e, he⟩ := _root_.GlobalTheory.locU_equiv_GL E n w hw
  obtain ⟨r, -, -, hc⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  let s : GL (Fin n) (w.adicCompletion E) →* UA E n :=
    (locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hs : ∀ y, cLoc w (s y) = y := fun y => by
    have := he (e.symm y)
    rw [e.apply_symm_apply] at this
    exact this.symm
  let P : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  have key : ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (τ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) X),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) τ →
      ∃ f : τ.IntertwiningMap (P.rep.comp s), f ≠ 0 := by
    rintro X _ _ τ ⟨-, f, h0, hf, h2⟩
    refine ⟨⟨f.codRestrict π hf, fun y => LinearMap.ext fun v => Subtype.ext ?_⟩, fun e0 => h0 ?_⟩
    · have h3 := h2 (e.symm y) v
      have hy : ((cLoc w).comp (locU n w).subtype) (e.symm y) = y := hs y
      rw [hy] at h3
      exact h3
    · exact LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun e0 v)
  obtain ⟨f, hf⟩ := key ρ₁ h₁
  obtain ⟨f', hf'⟩ := key ρ₂ h₂
  have hcomm : ∀ g : UA E n, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y) := fun g =>
    ⟨e (r g), fun y => by
      have : s (e (r g)) = (r g : UA E n) := congrArg Subtype.val (e.symm_apply_apply (r g))
      rw [this]
      exact hc g (e.symm y)⟩
  obtain ⟨q⟩ := (_root_.GlobalTheory.CuspRep.CompUniq.isotypic _ _ _ _ _ P.rep s ρ₁ ρ₂ P.isIrreducible_rep h₁.1 h₂.1 hcomm f hf).2 f' hf'
  exact GlobalTheory.BaseChangeBridge.hasSatGL_of_equiv q.toLinearEquiv
    (fun g x => LinearMap.congr_fun (q.toIntertwiningMap.isIntertwining' g) x) hT

end GlobalTheory.SplitSatake
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepresentableGlueOpenCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem homFixRep_glue_opens : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → ∀ (J : Type) (U : J → S.Opens), (∀ p : S, ∃ i, p ∈ U i) → (∀ i, ∃ (AU : Over (U i).toScheme) (_ : GrpObj AU) (BU : Over (U i).toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A (U i).ι φA ∧ IsGrpPullback BU B (U i).ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro S _ A B _ _ _ _ L M hA hB hL hM rA rB J U hU hloc
  refine _root_.GlobalTheory.EndLoc.HomGlue.homFixRep_glue (fun H A B _ _ _ _ L M Φ hΦ hA hB hL hM rA rB h => GlobalTheory.HomFixLocal.lbIso_pull_of_local H A B L M Φ hΦ hA hB hL hM rA rB h) S A B L M hA hB hL hM rA rB J (fun i => (U i).toScheme) (fun i => (U i).ι) (fun i => inferInstance) (fun s => ?_) (fun i => ?_)
  · obtain ⟨i, hi⟩ := hU s; exact ⟨i, by simpa [Scheme.Opens.range_ι] using hi⟩
  · obtain ⟨AU, gA, BU, gB, φA, φB, pA, pB, R, h1, h2, h3⟩ := hloc i; exact ⟨AU, BU, gA, gB, φA, φB, R, pA, pB, h1, h2, h3⟩

end GlobalTheory
end

