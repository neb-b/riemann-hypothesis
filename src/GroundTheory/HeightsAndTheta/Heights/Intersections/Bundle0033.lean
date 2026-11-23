module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0031

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.KerIsMultiHomogIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

attribute [local instance] MvPolynomial.weightedGradedAlgebra

namespace RegularityValuationCentre

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ltIdeal_one_isPrime {R Γ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ] (v : Valuation R Γ) :
    (v.ltIdeal 1).IsPrime := by
  refine ⟨fun h => ?_, fun {x y} hxy => ?_⟩
  · have h1 : (1 : v.integer) ∈ v.ltIdeal 1 := h ▸ Submodule.mem_top
    simp [Valuation.mem_ltIdeal_iff] at h1
  · simp only [Valuation.mem_ltIdeal_iff, Units.val_one] at hxy ⊢
    by_contra hc
    push Not at hc
    have hx : v x = 1 := le_antisymm x.2 hc.1
    have hy : v y = 1 := le_antisymm y.2 hc.2
    simp [Subring.coe_mul, map_mul, hx, hy] at hxy

def tWeight [DecidableEq K] (k : K) : K → ℕ := fun k' => if k' = k then 1 else 0


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem specMap_component [DecidableEq K] {E : Type*} [Field E] (ψ : MRing ι →+* E) (k : K) (d : ℕ)
    (g : MRing ι) :
    RegularityFunctionFieldNumber.specMap ψ ∅ (weightedHomogeneousComponent (blockWeight k) d g) =
      weightedHomogeneousComponent (tWeight k) d (RegularityFunctionFieldNumber.specMap ψ ∅ g) := by
  induction g using MvPolynomial.induction_on' with
  | monomial m c =>
    have hX : ∀ p : Σ k, ι k, IsWeightedHomogeneous (tWeight k)
        (RegularityFunctionFieldNumber.cS E ∅ p.1 * MvPolynomial.C (ψ (X p))) (tWeight k p.1) := by
      intro p
      simp only [RegularityFunctionFieldNumber.cS, Finset.notMem_empty, ite_false]
      rw [mul_comm]
      exact (isWeightedHomogeneous_X E (tWeight k) p.1).C_mul _
    have hh : IsWeightedHomogeneous (tWeight k) (RegularityFunctionFieldNumber.specMap ψ ∅ (monomial m c))
        (Finsupp.weight (blockWeight k) m) := by
      rw [RegularityFunctionFieldNumber.specMap, aeval_monomial, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum,
        show algebraMap ℤ (MvPolynomial K E) c = MvPolynomial.C (c : E) by simp]
      exact (IsWeightedHomogeneous.prod _ _ _ fun p _ => (hX p).pow (m p)).C_mul _
    have hm : IsWeightedHomogeneous (blockWeight k) (monomial m c) (Finsupp.weight (blockWeight k) m) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : d = Finsupp.weight (blockWeight k) m
    · rw [h, hm.weightedHomogeneousComponent_same, hh.weightedHomogeneousComponent_same]
    · rw [hm.weightedHomogeneousComponent_ne d h, hh.weightedHomogeneousComponent_ne d h, map_zero]
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), hp, hq, map_add (RegularityFunctionFieldNumber.specMap ψ ∅) p q]
    exact ((weightedHomogeneousComponent (R := E) (tWeight k) d).map_add _ _).symm


set_option backward.isDefEq.respectTransparency.types false in
theorem ker_isMultiHomogIdeal [DecidableEq K] {E : Type*} [Field E] (ψ : MRing ι →+* E) :
    IsMultiHomogIdeal (RingHom.ker (RegularityFunctionFieldNumber.specMap ψ ∅)) := by
  refine isMultiHomogIdeal_of_isHomogeneous fun k d g hg => ?_
  have hc : weightedHomogeneousComponent (blockWeight k) d g ∈ RingHom.ker (RegularityFunctionFieldNumber.specMap ψ ∅) := by
    rw [RingHom.mem_ker] at hg ⊢
    rw [specMap_component, hg, map_zero]
  rw [← weightedDecomposition.decompose'_apply] at hc
  exact hc

end RegularityValuationCentre


set_option maxHeartbeats 400000 in
open regularityEmbedding_holds in
theorem RegularityValuationCentre.proof : RegularityValuationCentre.Statement := by
  intro K _ ι _ P hP Γ _ v n hn
  classical
  obtain ⟨hPp, hPh, hPr⟩ := hP
  have := hPp
  have hX0 : ∀ {f : MRing ι}, f ∉ P → toFrac P f ≠ 0 := fun hf h => hf (toFrac_eq_zero.mp h)

  have hratio : ∀ (p : Σ k, ι k) (i : ι p.1), (X ⟨p.1, i⟩ : MRing ι) ∉ P → ∃ x : funField P,
      (x : FractionRing (MRing ι ⧸ P)) * toFrac P (X ⟨p.1, i⟩) = toFrac P (X p) := fun p i hi =>
    exists_funField_mul_eq (isMultiHomog_X_single p.1 p.2) (isMultiHomog_X_single p.1 i) hi
  choose j0 hj0 using hPr
  choose s hs using fun p : Σ k, ι k => hratio p (j0 p.1) (hj0 p.1)

  have hj : ∀ k, ∃ i, (X ⟨k, i⟩ : MRing ι) ∉ P ∧
      ∀ i', (X ⟨k, i'⟩ : MRing ι) ∉ P → v (s ⟨k, i'⟩) ≤ v (s ⟨k, i⟩) := by
    intro k
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i => (X ⟨k, i⟩ : MRing ι) ∉ P)
      (fun i => v (s ⟨k, i⟩)) ⟨j0 k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0 k⟩⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2,
      fun i' hi' => hmax i' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩)⟩
  choose j hjP hjmax using hj
  choose r hr using fun p : Σ k, ι k => hratio p (j p.1) (hjP p.1)

  have hrle : ∀ p, v (r p) ≤ 1 := by
    intro p
    by_cases hp : (X p : MRing ι) ∈ P
    · have h0 : r p = 0 := Subtype.ext <|
        (mul_eq_zero.mp ((hr p).trans (toFrac_eq_zero.mpr hp))).resolve_right (hX0 (hjP p.1))
      simp [h0]
    · obtain ⟨t, ht⟩ := hratio ⟨p.1, j0 p.1⟩ (j p.1) (hjP p.1)
      have hs' := hs ⟨p.1, j p.1⟩
      dsimp only at ht hs'
      have hst : s ⟨p.1, j p.1⟩ * t = 1 := Subtype.ext <| mul_right_cancel₀ (hX0 (hjP p.1)) <| by
        rw [Subring.coe_mul, Subring.coe_one, mul_assoc, ht, hs', one_mul]
      have hrs : r p * s ⟨p.1, j p.1⟩ = s p := Subtype.ext <| mul_right_cancel₀ (hX0 (hj0 p.1)) <| by
        rw [Subring.coe_mul, mul_assoc, hs', hr, hs]
      have hvs : v (s ⟨p.1, j p.1⟩) ≠ 0 := fun h => by
        have h1 := congrArg v hst
        rw [map_mul, h, zero_mul, map_one] at h1
        exact zero_ne_one h1
      have hle : v (r p) * v (s ⟨p.1, j p.1⟩) ≤ 1 * v (s ⟨p.1, j p.1⟩) := by
        rw [← map_mul, hrs, one_mul]
        exact hjmax p.1 p.2 hp
      exact le_of_mul_le_mul_right hle (zero_lt_iff.mpr hvs)

  have hψle : ∀ g, chartHom r g ∈ v.integer := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [chartHom]
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | mul_X f p hf =>
      rw [map_mul]
      exact mul_mem hf (by simpa [chartHom] using (Valuation.mem_integer_iff v (r p)).mpr (hrle p))
  have : (v.ltIdeal 1).IsPrime := RegularityValuationCentre.ltIdeal_one_isPrime v

  obtain ⟨E, _, ψE, hψE⟩ : ∃ (E : Type) (_ : Field E) (ψE : MRing ι →+* E),
      ∀ g, ψE g = 0 ↔ v (chartHom r g) < 1 := by
    refine ⟨FractionRing (v.integer ⧸ v.ltIdeal 1), inferInstance, (algebraMap (v.integer ⧸ v.ltIdeal 1) _).comp
      ((Ideal.Quotient.mk (v.ltIdeal 1)).comp ((chartHom r).codRestrict v.integer hψle)), fun g => ?_⟩
    rw [RingHom.comp_apply, RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _),
      Ideal.Quotient.eq_zero_iff_mem, Valuation.mem_ltIdeal_iff, Units.val_one]
    rfl

  have hform : ∀ (g : MRing ι) (a : K → ℕ), IsMultiHomog g a →
      (g ∈ RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅) ↔ v (chartHom r g) < 1) := by
    intro g a hg
    rw [RingHom.mem_ker, RegularityFunctionFieldNumber.specMap_form ψE ∅ hg, ← hψE, mul_eq_zero, MvPolynomial.C_eq_zero]
    refine or_iff_right (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ ?_)
    simp [RegularityFunctionFieldNumber.cS, MvPolynomial.X_ne_zero]
  have hWp : (RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅)).IsPrime := RingHom.ker_isPrime _
  have hPW : P ≤ RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅) := by
    obtain ⟨S, hS, hPS⟩ := hPh
    refine hPS.le.trans (Ideal.span_le.mpr fun g hg => ?_)
    obtain ⟨a, ha⟩ := hS g hg
    have hgP : g ∈ P := hPS ▸ Ideal.subset_span hg
    rw [SetLike.mem_coe, hform g a ha]
    have h1 := chartHom_mul j r hr ha
    rw [toFrac_eq_zero.mpr hgP] at h1
    have hφ : chartHom r g = 0 :=
      Subtype.ext ((mul_eq_zero.mp h1).resolve_right (toFrac_prod_ne_zero j hjP a))
    rw [hφ, map_zero]
    exact zero_lt_one
  have hC : IsMultiHomog (C n : MRing ι) 0 := fun μ hμ k => by
    rw [mem_support_iff, coeff_C] at hμ
    split_ifs at hμ with h
    · subst h
      simp
    · exact absurd rfl hμ
  refine ⟨RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅),
    ⟨hWp, RegularityValuationCentre.ker_isMultiHomogIdeal ψE, fun k => ⟨j k, ?_⟩⟩, hPW, ?_, fun z hz => ?_⟩
  ·
    have hrj : r ⟨k, j k⟩ = 1 :=
      Subtype.ext (mul_right_cancel₀ (hX0 (hjP k)) ((hr ⟨k, j k⟩).trans (one_mul _).symm))
    rw [hform _ _ (isMultiHomog_X_single k (j k))]
    have hXr : chartHom r (X ⟨k, j k⟩) = r ⟨k, j k⟩ := eval₂Hom_X' _ _ _
    rw [hXr, hrj, Valuation.map_one]
    exact lt_irrefl 1
  · rw [hform _ 0 hC]
    have hCn : chartHom r (C n) = (n : funField P) := eval₂Hom_C _ _ _
    rw [hCn]
    exact hn
  ·
    obtain ⟨u, w, a, hu, hw, hwW, e⟩ := LocRingFrac.proof K ι P _ hPp hWp hPW z hz
    have hzw : z * chartHom r w = chartHom r u :=
      Subtype.ext <| mul_right_cancel₀ (toFrac_prod_ne_zero j hjP a) <| by
        rw [Subring.coe_mul, mul_assoc, chartHom_mul j r hr hw, chartHom_mul j r hr hu]
        exact e
    have hvw : v (chartHom r w) = 1 :=
      le_antisymm (hψle w) (not_lt.mp fun h => hwW ((hform w a hw).mpr h))
    have h1 := congrArg v hzw
    rw [map_mul, hvw, mul_one] at h1
    exact h1 ▸ hψle u

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PDeSlotAdd
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem ptsIntegral_eq_zero_of_vanish (P : Ideal (MRing ι)) {e : ℕ}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) {g : ((Σ k, ι k) → ℂ) → ℝ}
    (hg : ∀ z ∈ mcPts P, g z = 0) : ptsIntegral P φ g = 0 := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have h0 : ∀ y w, sheetDensity P hΨ.choose φ g y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1, zero_mul]
      · rfl
    simp [h0]
  · rfl

theorem ptsIntegral_update_tensor (hE : ResExistsStatement) {P : Ideal (MRing ι)} {e : ℕ}
    (hP : IsArithVar P (e + 1)) {L : Fin e → HermLine ι} (j : Fin e) {M N A : HermLine ι}
    {s : MRing ι} (hL : ∀ i, IsSmoothHerm (L i)) (hM : IsSmoothHerm M) (hN : IsSmoothHerm N)
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ptsIntegral P (pot (Function.update L j (M.tensor N))) (logNorm A s) =
      ptsIntegral P (pot (Function.update L j M)) (logNorm A s) +
        ptsIntegral P (pot (Function.update L j N)) (logNorm A s) := by
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 1 := ⟨e - 1, by have := j.pos; omega⟩
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  set T : Fin m → HermLine ι := fun i => L (Equiv.swap 0 j i.succ) with hT
  have hT' : ∀ i, IsSmoothHerm (T i) := fun i => hL _
  have hU : ∀ X : HermLine ι, IsSmoothHerm X → ∀ i, IsSmoothHerm (Function.update L j X i) := by
    intro X hX i
    rcases eq_or_ne i j with rfl | h
    · simpa using hX
    · rw [Function.update_of_ne h]
      exact hL i
  have hC : ∀ X : HermLine ι, IsSmoothHerm X →
      ∀ i, IsSmoothHerm ((Fin.cons X T : Fin (m + 1) → HermLine ι) i) :=
    fun X hX i => Fin.cases hX hT' i
  have key : ∀ X : HermLine ι, IsSmoothHerm X →
      ptsIntegral P (pot (Function.update L j X)) (logNorm A s) =
        mInt R.A (Fin.cons (potOf R X) fun i => potOf R (T i))
          (fun x => logNorm A s (R.lift x x)) := by
    intro X hX
    rw [ptsIntegral_eq_mInt' hE resBridge R hP (hU X hX) hA hs, ← potOf_cons R X T,
      ← mIntSymm R.A (fun i => potOf R (Function.update L j X i)) (Equiv.swap 0 j)]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · have hne : Equiv.swap 0 j i.succ ≠ j := by
        intro h
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
        exact Fin.succ_ne_zero _ h
      simp only [Function.comp_apply, Fin.cons_succ, hT, Function.update_of_ne hne]
  rw [key _ (isSmoothHerm_tensor hM hN), key M hM, key N hN]
  have hΦ : ∀ i, IsPotential R.A (potOf R (T i)) := fun i => isPotential_potOf R (hT' i)
  have hPM := isPotential_potOf R hM
  have hPN := isPotential_potOf R hN
  have e1 : mInt R.A (Fin.cons (potOf R (M.tensor N)) fun i => potOf R (T i))
      (fun x => logNorm A s (R.lift x x)) =
      mInt R.A (Fin.cons (potOf R M + potOf R N) fun i => potOf R (T i))
        (fun x => logNorm A s (R.lift x x)) := by
    refine ReciprocityTheory.ChartRestriction.G.Geo.mInt_congr _ (locDens_cons_congr _ _ fun j y hy =>
      germ_of_eqOn R (fun x z hz => ?_) j y hy) fun _ => rfl
    have hm := (R.mem x z hz).1
    show Real.log (M.h (R.lift x z) * N.h (R.lift x z)) =
      Real.log (M.h (R.lift x z)) + Real.log (N.h (R.lift x z))
    exact Real.log_mul (M.pos _ hm).ne' (N.pos _ hm).ne'
  have hI : ∀ X : HermLine ι, IsSmoothHerm X →
      MIntegrable R.A (Fin.cons (potOf R X) fun i => potOf R (T i))
        (fun x => logNorm A s (R.lift x x)) := by
    intro X hX
    rw [← potOf_cons R X T]
    exact brIntegrable R _ A s hP (hC X hX) hA hs
  rw [e1]
  exact mIntAdd R.A _ _ _ hPM hPN hΦ _ (hI M hM) (hI N hN)

theorem DeSlotAdd.proof (hE : ResExistsStatement) : DeSlotAdd.Statement := by
  intro K _ ι _ P n L j M N A A' s s' hP hL hM hN hA hA' hs hs' _

  have hZ : ∀ (B C : HermLine ι) (t : MRing ι), IsSmoothHerm B → IsSmoothHerm C →
      IsSectionOn P C t →
      ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot (Function.update L j (M.tensor N))))
          (logNorm C t) =
        ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot (Function.update L j M)))
            (logNorm C t) +
          ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot (Function.update L j N)))
            (logNorm C t) := by
    intro B C t hB hC ht
    have hc : ∀ X : HermLine ι,
        (Fin.cons (fun z => Real.log (B.h z)) (pot (Function.update L j X)) :
          Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) =
          pot (Function.update (Fin.cons B L : Fin (n + 1) → HermLine ι) j.succ X) := by
      intro X
      rw [← Fin.cons_update]
      funext i
      exact Fin.cases rfl (fun i => rfl) i
    rw [hc, hc, hc]
    exact ptsIntegral_update_tensor hE hP j.succ (fun i => Fin.cases hB hL i) hM hN hC ht

  have hW : ∀ (t t' : MRing ι) (C C' : HermLine ι), IsSectionOn P C t → IsSmoothHerm C' →
      IsSectionOn P C' t' →
      (∑ᶠ (W) (_ : W ∈ divSupp P t ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
          ptsIntegral W (pot (Function.update L j (M.tensor N))) (logNorm C' t')) =
        (∑ᶠ (W) (_ : W ∈ divSupp P t ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
            ptsIntegral W (pot (Function.update L j M)) (logNorm C' t')) +
          (∑ᶠ (W) (_ : W ∈ divSupp P t ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
            ptsIntegral W (pot (Function.update L j N)) (logNorm C' t')) := by
    intro t t' C C' ht hC' ht'
    have hfin : {W | W ∈ divSupp P t ∧ IsHorizontal W}.Finite :=
      (divSupp_finite P t).subset fun W hW => hW.1
    have hpt : ∀ W ∈ {W | W ∈ divSupp P t ∧ IsHorizontal W},
        (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
            ptsIntegral W (pot (Function.update L j (M.tensor N))) (logNorm C' t') =
          (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
              ptsIntegral W (pot (Function.update L j M)) (logNorm C' t') +
            (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
              ptsIntegral W (pot (Function.update L j N)) (logNorm C' t') := by
      intro W hW
      rw [← mul_add]
      congr 1
      have hWa : IsArithVar W (n + 1) := (divSuppArith K ι P (n + 1) C t W hP ht hW.1).1 hW.2
      by_cases hsW : t' ∈ W
      · have h0 : ∀ z ∈ mcPts W, logNorm C' t' z = 0 := by
          intro z hz
          simp [logNorm, hz.2 t' hsW]
        rw [ptsIntegral_eq_zero_of_vanish W _ h0, ptsIntegral_eq_zero_of_vanish W _ h0,
          ptsIntegral_eq_zero_of_vanish W _ h0, add_zero]
      · obtain ⟨a, ha, hta, -⟩ := ht'
        exact ptsIntegral_update_tensor hE hWa j hL hM hN hC' ⟨a, ha, hta, hsW⟩
    show ∑ᶠ W ∈ {W | W ∈ divSupp P t ∧ IsHorizontal W}, (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
          ptsIntegral W (pot (Function.update L j (M.tensor N))) (logNorm C' t') =
        ∑ᶠ W ∈ {W | W ∈ divSupp P t ∧ IsHorizontal W}, (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
            ptsIntegral W (pot (Function.update L j M)) (logNorm C' t') +
          ∑ᶠ W ∈ {W | W ∈ divSupp P t ∧ IsHorizontal W}, (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
            ptsIntegral W (pot (Function.update L j N)) (logNorm C' t')
    rw [← finsum_mem_add_distrib hfin]
    exact finsum_mem_congr rfl hpt
  unfold De
  rw [hW s s' A A' hs hA' hs', hW s' s A' A hs' hA hs, hZ A' A s hA' hA hs, hZ A A' s' hA hA' hs']
  ring

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem isSmoothHerm_of_isPullHerm' {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : HermLine ι} {A' : HermLine ι'} (hA : IsSmoothHerm A) (h : IsPullHerm κ v A A') :
    IsSmoothHerm A' := by
  have e : A'.h = A.h ∘ fun z' p => z' (v p) := funext h.2
  unfold IsSmoothHerm
  rw [e]
  refine hA.comp (contDiff_pi.2 fun p => contDiff_apply ℝ (fun _ => ℂ) (v p)).contDiffOn ?_
  intro z' hz'
  simp only [Set.mem_ofPred_eq] at hz' ⊢
  intro k
  obtain ⟨i', hi'⟩ := hz' (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩

theorem arithDim_lt_of_lt {P Q : Ideal (MRing ι)} {d d₀ : ℕ} (hP : IsArithVar P d) (hQ : IsArithVar Q d₀)
    (hle : P ≤ Q) (hne : P ≠ Q) : d₀ < d := by
  obtain ⟨f, hfQ, hfP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  have := hP.2.1.1
  have hf0 : Ideal.Quotient.mk P f ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hf0)
  have h2 : ringKrullDim (MRing ι ⧸ Q) ≤
      ringKrullDim ((MRing ι ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P f}) := by
    refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor hle) ?_) ?_
    · intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hfQ, mul_zero]
    · intro z
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk P z), rfl⟩
  rw [hP.2.2.2] at h1
  rw [hQ.2.2.2] at h2
  have h3 : ((d₀ + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    le_trans (by gcongr) h1
  have h4 : ((d₀ + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast h3
  have h5 : d₀ + Fintype.card K + 1 ≤ d + Fintype.card K := by exact_mod_cast h4
  omega

end SlopeTestRemainingChoices

theorem PFStep.proof (hSec : PFSecRed.Statement) (hVert : PFVert.Statement) (hInt : PFIntZero.Statement)
    (hHor : PFHoriz.Statement) (hSum : PFFibreSum.Statement) (hIm : ImageArithStatement) (hCM : ContractMixedStatement) : PFStep.Statement := by
  intro I hI r hr
  refine hSec I hI r ?_
  intro K _ ι _ K' _ ι' _ κ v P' d G J L L' N s a hv hP' hP hJ hL hL' hN ha hs hsP
  have hP1 : IsArithVar P' (d + r + 1) := hP'
  have hsec : IsSectionOn P' (N (Fin.last r)) s := ⟨a, ha, hs, hsP⟩
  have hM : ∀ j, IsSmoothHerm (Fin.append L' (Fin.init N) j) := by
    intro j
    induction j using Fin.addCases with
    | left i => rw [Fin.append_left]; exact isSmoothHerm_of_isPullHerm' hv (hL i) (hL' i)
    | right i => rw [Fin.append_right]; exact hN _
  have hR := (hI K' ι').2.2 P' (d + r) (Fin.append L' (Fin.init N)) (N (Fin.last r)) s a hP1 hM (hN _) ha hs hsP
  rw [← Fin.append_snoc, Fin.snoc_init_self] at hR
  refine hR.trans ?_
  rw [recR_eq, hInt K ι K' ι' κ v P' d r L L' (Fin.init N) (N (Fin.last r)) s hv hP1 hP hL hL', sub_zero, cycR,
    ← hSum K ι K' ι' κ v P' d r G J N s a hv hP1 hP hJ ha hs hsP, finsum_mem_mul]
  refine finsum_mem_congr rfl fun W hW => ?_
  by_cases hh : IsHorizontal W
  · have hWa : IsArithVar W (d + r) := (divSuppArith K' ι' P' (d + r) (N (Fin.last r)) s W hP1 hsec hW).1 hh
    by_cases hd : imageZ v W = imageZ v P'
    · rw [if_pos hh, if_pos ⟨hh, hd⟩,
        hHor I r hr K ι K' ι' κ v P' W d G J L L' (Fin.init N) hv hWa hd hP hJ hL hL' (fun j => hN _)]
      exact (mul_assoc _ _ _).symm
    · rw [if_pos hh, if_neg (fun h => hd h.2), mul_zero, zero_mul]
      obtain ⟨d₀, -, hd₀⟩ := hIm K ι K' ι' κ v W (d + r) hP.1 hv hWa
      have hle : imageZ v P' ≤ imageZ v W := Ideal.comap_mono (le_sup_left.trans hW.1.1.2)
      rw [hCM I hI K ι K' ι' κ v W d₀ d r L L' (Fin.init N) hv hWa hd₀
        (arithDim_lt_of_lt hP hd₀ hle (Ne.symm hd)) hL hL' (fun j => hN _), mul_zero]
  · rw [if_neg hh, if_neg (fun h => hh h.1),
      hVert K ι K' ι' κ v P' d r L L' (Fin.init N) s a W hv hP1 hP hL' hs hsP hW hh]
    simp

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingInj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W W' : Ideal (MRing ι)),
    P.IsPrime → IsMultiProjPrime W → IsMultiProjPrime W' → P ≤ W → P ≤ W' →
    locRing P W = locRing P W' → W = W'

end

end GroundTheory.Heights₂.Heights.Inter
end

