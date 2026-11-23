module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TensorActionApplyDual
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.InnerCompactWordActionAdjoint
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0016
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.LiftHighestWeightVector
section
noncomputable section

open Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.LowestWeightLiftLemmas

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.LemK

variable {n : ℕ}

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem lc_adLW (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) (x : M) :
    ∀ w : List (Fin n × Fin n),
      Finsupp.linearCombination ℂ (fun w' => wordE E w' x) (adLW a b w) =
        E a b (wordE E w x) - wordE E w (E a b x) := by
  intro w
  induction w with
  | nil => simp [adLW, wordE]
  | cons p w ih =>
    obtain ⟨c, d⟩ := p
    have h1 : Finsupp.linearCombination ℂ (fun w' => wordE E w' x) ((adL a b (c, d)).mapDomain (· :: w)) =
        E a b (E c d (wordE E w x)) - E c d (E a b (wordE E w x)) := by
      rw [Finsupp.linearCombination_mapDomain]
      have hg := congrArg (fun T : Module.End ℂ M => T (wordE E w x)) (hE a b c d)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at hg
      rw [hg, adL, map_sub]
      simp only [Function.comp_def, wordAction_cons]
      congr 1 <;> split_ifs with h <;> simp_all
    have h2 : Finsupp.linearCombination ℂ (fun w' => wordE E w' x) ((adLW a b w).mapDomain ((c, d) :: ·)) =
        E c d (Finsupp.linearCombination ℂ (fun w' => wordE E w' x) (adLW a b w)) := by
      rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]
      congr 1
    simp only [adLW, map_add (f := _)]
    rw [h1, h2, ih, wordAction_cons, wordAction_cons, map_sub]
    abel

theorem contraction_compactWordAction (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (hE : IsGlRep E) (a b : Fin n) (hab : ε a = ε b)
    (x : KS (n := n) V) (d : Fin n) : sT E V (Cone.compactWordAction ε E V hV a b x) d = E a b (sT E V x d) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]
  | single p v =>
    obtain ⟨w, c⟩ := p
    have key := lc_adLW E hE a b (v : M) w
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at key
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Cone.compactWordAction_single, dite_eq_left hab, map_add (f := _), map_sum, sT_single, Pi.add_apply, Finset.sum_apply]
    simp only [map_smul, sT_single, Pi.smul_apply]
    by_cases hd : d = c
    · subst hd
      simp only [Pi.single_eq_same]
      rw [key, sub_add_cancel]
    · simp [hd]

theorem sT_sA (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (hE : IsGlRep E) (a b : Fin n) (hab : ε a = ε b) (x : KS (n := n) V) :
    sT E V (sA ε E V hV a b x) = tensV E a b (sT E V x) := by
  have e : sA ε E V hV a b x = Cone.compactWordAction ε E V hV a b x + Cone.sC V a b x := by
    simp [Cone.compactWordAction]
  funext d
  rw [e, map_add (f := _), Pi.add_apply, contraction_compactWordAction ε E V hV hE a b hab, Cone.sT_sC, Cone.tensV_eq]

theorem sA_single' (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (a b : Fin n) (p : List (Fin n × Fin n) × Fin n) (v : V) :
    sA ε E V hV a b (Finsupp.single p v) =
      (∑ w' ∈ (adLW a b p.1).support, adLW a b p.1 w' • Finsupp.single (w', p.2) v) +
      (if h : ε a = ε b then Finsupp.single p ⟨E a b v, hV a b h v v.2⟩ else 0) +
      (if p.2 = b then Finsupp.single (p.1, a) v else 0) := by
  simp only [sA, Finsupp.lsum_single, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Finsupp.lsingle_apply]
  congr 1
  · congr 1
    split_ifs <;> rfl
  · split_ifs <;> rfl

end Alg

section IP

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem ipK_sC (V : Submodule ℂ M) (a b : Fin n) (x y : KS (n := n) V) :
    Cone.ipK V (Cone.sC V a b x) y = Cone.ipK V x (Cone.sC V b a y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']
  | single p v =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' h h' => simp only [map_add (f := _), h, h']
    | single q u =>
      obtain ⟨w, c⟩ := p
      obtain ⟨w', c'⟩ := q
      rw [Cone.sC_single, Cone.sC_single]
      by_cases h1 : c = b <;> by_cases h2 : c' = a <;>
        simp [h1, h2, Cone.ipK_single, Finsupp.single_apply, Prod.ext_iff]

theorem ipK_sA (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (hU : IsKUnitary ε E) {a b : Fin n} (hab : ε a = ε b)
    (x y : KS (n := n) V) : Cone.ipK V (sA ε E V hV a b x) y = Cone.ipK V x (sA ε E V hV b a y) := by
  have e : ∀ a b (z : KS (n := n) V), sA ε E V hV a b z = Cone.compactWordAction ε E V hV a b z + Cone.sC V a b z := by
    intro a b z; simp [Cone.compactWordAction]
  rw [e, e, map_add (f := _), LinearMap.add_apply, map_add (f := _), Cone.inner_compactWordAction_adjoint hV hU hab, ipK_sC]

theorem lift_highestWeightVector {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) (hV : IsKStableSub ε E V)
    [FiniteDimensional ℂ V] (hE : IsGlRep E)
    (hU : ∀ a b, ε a = ε b → ∀ x y : M, ⟪E a b x, y⟫_ℂ = ⟪x, E b a y⟫_ℂ)
    (μ : Fin n → ℝ) (f : Fin n → M) (hf : ∀ c, f c ∈ genSub E V) (hμ : IsKHWVec ε (tensV E) μ f) :
    ∃ u, IsKHWVec ε (sA ε E V hV) μ u ∧ sT E V u = f := by
  have hU' : IsKUnitary ε E := hU
  obtain ⟨x, rfl⟩ := sT_surj E V f hf
  set R := x.support.sup fun p => p.1.length with hR
  let S : Set (List (Fin n × Fin n) × Fin n) := {p | p.1.length ≤ R}
  have hSf : S.Finite := ((List.finite_length_le (Fin n × Fin n) R).prod Set.finite_univ).subset
    fun p hp => ⟨hp, trivial⟩
  have := hSf.to_subtype
  have hfd : FiniteDimensional ℂ (Finsupp.supported V ℂ S) :=
    Module.Finite.equiv (Finsupp.supportedEquivFinsupp (M := V) (R := ℂ) S).symm
  have hS : IsKStableSub ε (sA ε E V hV) (Finsupp.supported V ℂ S) := by
    intro a b hab y hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finsupp.sum_single y, Finsupp.sum, map_sum]
    refine Submodule.sum_mem _ fun p hp => ?_
    have hpS : p.1.length ≤ R := hy hp
    rw [sA_single']
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun w' hw' =>
      Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℂ _ ?_)) ?_) ?_
    · show w'.length ≤ R
      rw [TRA.adLW_length a b _ _ hw']; exact hpS
    · rw [dite_eq_left hab]
      exact Finsupp.single_mem_supported ℂ _ hpS
    · split_ifs
      · exact Finsupp.single_mem_supported ℂ _ (show p.1.length ≤ R from hpS)
      · exact Submodule.zero_mem _
  let cr : InnerProductSpace.Core ℂ (KS (n := n) V) :=
    { inner := fun x y => Cone.ipK V x y
      conj_inner_symm := fun x y => Cone.ipK_symm x y
      re_inner_nonneg := fun x => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Cone.ipK_apply, map_sum]; exact sum_nonneg fun p _ => inner_self_nonneg
      add_left := fun x y z => by rw [map_add (f := _), LinearMap.add_apply]
      smul_left := fun x y r => by rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
      definite := fun x hx => by
        have h1 := congrArg RCLike.re hx
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Cone.ipK_apply, map_sum, map_zero,
          sum_eq_zero_iff_of_nonneg fun p _ => inner_self_nonneg] at h1
        ext1 p
        by_cases hp : p ∈ x.support
        · have h2 := h1 p hp
          rw [inner_self_eq_norm_sq] at h2
          exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
        · exact Finsupp.notMem_support_iff.mp hp }
  let _ : NormedAddCommGroup (KS (n := n) V) := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ cr
  let _ : InnerProductSpace ℂ (KS (n := n) V) := InnerProductSpace.ofCore cr.toCore
  obtain ⟨u, -, -, h1, h2⟩ := lift_khw (ε := ε) (A := sA ε E V hV) (μ := μ)
    (B := tensV E) (fun a b hab x y => ipK_sA ε E V hV hU' hab x y) (sT E V)
    (fun a b hab x => sT_sA ε E V hV hE a b hab x) hfd hS (x₀ := x)
    (fun p hp => Finset.le_sup (f := fun p : List (Fin n × Fin n) × Fin n => p.1.length) hp) hμ
  exact ⟨u, h1, h2⟩

end IP

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.LowestWeightLiftLemmas
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SchmidCas
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section No

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem sc_no_of_schmid (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) (hn : (n : ℝ) < h)
    (hS : ∀ x ∈ Wm ε E V, phi E 1 x = 0) :
    ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1,
      IsKHWVec ε E (lowK ε lam - root a b) w → w = 0 := by
  intro a b hab hε w hw hμ
  by_contra hw0
  have : FiniteDimensional ℂ V := hV.1
  have hKU : IsKUnitary ε E := isKUnitary_of_isInfUnitary hU
  have hP : V.starProjection w = 0 := by
    by_contra hne
    have hkhw := isKHWVec_starProjection hKU hV.2.1 hμ
    have heq := khw_weight_eq_of_irr hE hV (Submodule.starProjection_apply_mem V w) hne hkhw
    have h2 := congr_fun heq a
    simp only [Pi.sub_apply, root, Pi.single_eq_same, Pi.single_eq_of_ne hab.ne] at h2
    linarith
  have hperp : ∀ u ∈ layer ε E V 0, inner ℂ u w = 0 := by
    intro u hu
    have hwo : w ∈ Vᗮ := by
      have := Submodule.sub_starProjection_mem_orthogonal (K := V) w
      rwa [hP, sub_zero] at this
    exact (Submodule.mem_orthogonal V w).1 hwo u hu
  obtain ⟨P, hPnc, hP0, hPμ, hPperp⟩ := lift_layer hE hU hV.1 hV.2.1 (k := 0) hw hperp hμ hw0
  obtain ⟨xm, hxm, xp, hxp, hsum⟩ := ncV_one_decomp hE hU hV hmono hh hbig hPnc
  have hxm0 : inner ℂ xm P = 0 :=
    hPperp xm (Wm_le_ncV hxm) (by rw [hS xm hxm]; exact zero_mem _)
  have hmp : inner ℂ xm xp = 0 := Wm_perp_Wp hU hxm hxp
  have hxm_eq : xm = 0 := by
    have h3 : inner ℂ xm xm = 0 := by
      rw [hsum, inner_add_right, hmp, add_zero] at hxm0
      exact hxm0
    exact inner_self_eq_zero.1 h3
  rw [hxm_eq, zero_add] at hsum
  have hPWp : P ∈ Wp ε E V := hsum ▸ hxp
  obtain ⟨r, s, -, -, hC⟩ := crossOp_khw hE hU hV hPnc hP0 hPμ
  have hroot : lowK ε lam - root a b = lowK ε lam + root b a := by
    ext x; simp only [Pi.sub_apply, Pi.add_apply, root]; ring
  have hneg := crossVal_neg hmono hh hab hε
  rw [← hroot] at hneg
  have hWp := Wp_bound hE hU hV hmono hh hbig hPWp
  set val : ℝ := casValK ε (lowK ε lam - root a b) - n - casValK ε (lowK ε lam) with hval
  have key : 2 * RCLike.re (inner ℂ (crossOp ε E 1 0 P) P) = val * ‖P‖ ^ 2 := by
    have e := congrArg (fun x => RCLike.re (inner ℂ x P)) hC
    have hre : ((‖P‖ : ℂ) ^ 2).re = ‖P‖ ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
    simp only [inner_smul_left, inner_self_eq_norm_sq_to_K] at e
    simp at e
    rw [hre] at e
    exact e
  have hpos : 0 < ‖P‖ ^ 2 := by positivity
  have h4 : 2 * (h - n + 1) * ‖P‖ ^ 2 ≤ (-2 * h - 2) * ‖P‖ ^ 2 := by
    rw [key] at hWp
    exact hWp.trans (mul_le_mul_of_nonneg_right hneg hpos.le)
  have h5 := le_of_mul_le_mul_right h4 hpos
  linarith

end No

theorem schmid_casimir (n : ℕ) : SchmidCasimirStatement n := by
  intro ε ν h c N _ _ EN W hE hU hW hS hc hint hmono hgap hneed hp hq
  set lam : Fin n → ℝ := ν + rhoC ε - rhoN ε with hlam
  have hlow : lowK ε lam = ν := by
    ext a; simp only [lowK, hlam, Pi.add_apply, Pi.sub_apply]; ring
  have hW' : IsKIrrHW ε EN (lowK ε lam) W := by rw [hlow]; exact hW
  have hN1 : 2 + (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) ≤ hNeed ε := by
    unfold hNeed
    exact le_trans (by linarith [le_max_right (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))])
      (le_max_left _ _)
  have hN2 : 2 + 3 * (n : ℝ) / 2 ≤ hNeed ε := by
    unfold hNeed
    exact le_trans (by linarith [le_max_left (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))])
      (le_max_left _ _)
  have hN3 : 16 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) + 8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) + 2
      ≤ hNeed ε := (le_max_left _ _).trans (le_max_right _ _)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h := by linarith
  have hn : (n : ℝ) < h := by linarith
  have hstd : StdGap ε lam := ⟨hmono, h, hgap, hbig⟩
  have hHC : S7.IsHCParam lam := ⟨hmono, hint⟩
  obtain ⟨T⟩ := HW.kType_exists ε lam hHC
  obtain ⟨μ, hμ⟩ := S7.exists_mu hHC
  have hq0 : 1 ≤ S7.q0 ε := le_min hp hq
  have h8 : 8 * (n : ℝ) * (S7.q0 ε : ℝ) < h := by
    have e : ((S7.q0 ε : ℕ) : ℝ) = (min (pOf ε) (qOf ε) : ℝ) := by
      simp only [S7.q0, Nat.cast_min]
    have hm : 0 ≤ (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) := by positivity
    have hs := Real.sqrt_nonneg (2 * (min (pOf ε) (qOf ε) : ℝ))
    rw [e]
    nlinarith
  have hPsi := (S7.isPsiFor_psiM ε lam h T μ hHC hμ hgap hq0 h8).1
  have hv₀ : T.w ≠ 0 := by
    intro h0
    have h1 := T.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hcas := casimir_eq_casVal_of_model hstd hE hU hW'
    (sc_no_of_schmid hE hU hW' hmono hgap hbig hn hS) hD.glRep (isInfUnitary_of_isDerivedOn hσ hD)
    (datumV_isKIrrHW hPsi hv₀) (datumV_casimir hPsi T.w)
  obtain ⟨w, hwW, hw0, -⟩ := hW.2.2.2
  have h1 := hc w hwW
  rw [hcas w hwW] at h1
  simpa using (smul_left_injective ℂ hw0 h1).symm

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

