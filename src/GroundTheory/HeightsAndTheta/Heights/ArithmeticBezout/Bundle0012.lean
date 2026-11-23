module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowFormHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem aeval_scale_of_isWeightedHomogeneous {σ R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] {w : σ → ℕ} {p : MvPolynomial σ R} {a : ℕ} (hp : IsWeightedHomogeneous w p a)
    (t : A) (u : σ → A) : aeval (fun j => t ^ w j * u j) p = t ^ a * aeval u p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  have hw : ∑ j ∈ d.support, w j * d j = a := by
    rw [← hp (mem_support_iff.mp hd), Finsupp.weight_apply, Finsupp.sum]
    simp [smul_eq_mul, mul_comm]
  rw [hw]
  ring

variable {F : Type} [Field F] {n k : ℕ}

theorem scale_mem_incidence {I : Ideal (MvPolynomial (Fin n) F)}
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence I k) (i : Fin k)
    (t : AlgebraicClosure F) : (fun ij => t ^ inGroup i ij * u ij) ∈ incidence I k := by
  obtain ⟨x, hx0, hxI, hux⟩ := hu
  refine ⟨x, hx0, hxI, fun i' => ?_⟩
  have hc : ∀ j : Fin n, t ^ inGroup i (i', j) * u (i', j) * x j =
      t ^ (if i' = i then 1 else 0) * (u (i', j) * x j) := fun j => by rw [mul_assoc]; rfl
  refine Eq.trans (Finset.sum_congr rfl fun j _ => hc j) ?_
  rw [← Finset.mul_sum, hux i', mul_zero]

theorem component_vanish_incidence {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : ∀ u ∈ incidence I k, aeval u f = 0) (i : Fin k)
    {a : ℕ} (ha : a ∈ weightSet (inGroup (n := n) i) f) :
    ∀ u ∈ incidence I k, aeval u (weightedHomogeneousComponent (inGroup (n := n) i) a f) = 0 := by
  classical
  intro u hu
  set w := inGroup (n := n) i
  set S := weightSet w f
  set q : Polynomial (AlgebraicClosure F) :=
    ∑ b ∈ S, Polynomial.C (aeval u (weightedHomogeneousComponent w b f)) * Polynomial.X ^ b with hq_def
  have hq : q = 0 := by
    apply Polynomial.funext
    intro t
    have h1 := hf _ (scale_mem_incidence hu i t)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← sum_weightSet_component (w := w) f, map_sum] at h1
    simp only [hq_def, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    rw [← h1]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [aeval_scale_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous b f),
      mul_comm]
  have hc := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p a) hq
  simp only [hq_def, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hc
  rw [Finset.sum_ite_eq, if_pos ha] at hc
  exact hc

theorem IsChowForm.exists_isWeightedHomogeneous_inGroup {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (i : Fin k) :
    ∃ a, IsWeightedHomogeneous (inGroup (n := n) i) f a := by
  obtain ⟨a, ha⟩ := weightSet_nonempty (w := inGroup (n := n) i) hf.1
  have hvan : ∀ u ∈ incidence I k, aeval u f = 0 := (hf.2 f).mpr dvd_rfl
  obtain ⟨r, hr⟩ := (hf.2 _).mp (component_vanish_incidence hvan i ha)
  have hc := component_ne_zero_of_mem ha
  rw [hr] at hc
  refine isWeightedHomogeneous_of_mul_left (m := a) ?_ hf.1 (right_ne_zero_of_mul hc)
  rw [← hr]
  exact weightedHomogeneousComponent_isWeightedHomogeneous a f

theorem zero_mem_incidence {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P) (k : ℕ) :
    (0 : Fin k × Fin n → AlgebraicClosure F) ∈ incidence P k := by
  obtain ⟨j, hj⟩ := hP.isRelevant
  have hex : ∃ x ∈ zeroLocus (AlgebraicClosure F) P, x ≠ 0 := by
    by_contra h
    push Not at h
    apply hj
    have hrad : X j ∈ vanishingIdeal F (zeroLocus (AlgebraicClosure F) P) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [h x hx]
      simp
    rwa [vanishingIdeal_zeroLocus_eq_radical, hP.isPrime.radical] at hrad
  obtain ⟨x, hx, hx0⟩ := hex
  exact ⟨x, hx0, fun g hg => mem_zeroLocus_iff.mp hx g hg, fun i => by simp⟩

theorem IsChowForm.exists_multiHomog {P : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hP : IsProjPrime P) (hf : IsChowForm P k f) :
    ∃ δ, 1 ≤ δ ∧ IsMultiHomog δ f := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    exact ⟨1, le_rfl, fun d _ => funext fun i => i.elim0⟩
  choose a ha using fun i => hf.exists_isWeightedHomogeneous_inGroup i
  have hδ : IsMultiHomog (a ⟨0, hk⟩) f := (isMultiHomog_iff _ _).mpr fun i => by
    rw [hf.degrees_eq ha ⟨0, hk⟩ i]
    exact ha i
  refine ⟨a ⟨0, hk⟩, Nat.one_le_iff_ne_zero.mpr fun h0 => ?_, hδ⟩
  rw [h0] at hδ
  have hd0 : ∀ d ∈ f.support, d = 0 := by
    intro d hd
    have h := congrFun (hδ (mem_support_iff.mp hd))
    ext ij
    by_contra hne
    have h1 := h ij.1
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at h1
    have h2 := (Finset.sum_eq_zero_iff.mp h1) ij (Finsupp.mem_support_iff.mpr hne)
    simp [groupWeight] at h2
    exact hne h2
  have hC : f = C (AddMonoidAlgebra.coeff f 0) := by
    ext d
    rw [coeff_C]
    split_ifs with hd
    · rw [hd]
    · by_contra hne
      exact hd (hd0 d (mem_support_iff.mpr hne)).symm
  have hz := (hf.2 f).mpr dvd_rfl 0 (zero_mem_incidence hP k)
  rw [hC, aeval_C, map_eq_zero_iff _ (algebraMap F (AlgebraicClosure F)).injective] at hz
  exact hf.1 (by rw [hC, hz, C_0])

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.HeightMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

theorem chowHeightMul_of_mahlerMul (hM : MahlerMul.Statement) : ChowHeightMul.Statement := by
  intro K _ _ n H k δ₁ δ₂ f₁ f₂ h₁ h₂
  unfold chowHt
  have hmah : ∀ σ : K →+* ℂ, mahler (H.normAt σ) k ((f₁ * f₂).map σ) =
      mahler (H.normAt σ) k (f₁.map σ) + mahler (H.normAt σ) k (f₂.map σ) := by
    intro σ
    rw [map_mul]
    exact hM n k _ _ _ (fun h => h₁ (map_injective σ σ.injective (by rw [h, map_zero])))
      (fun h => h₂ (map_injective σ σ.injective (by rw [h, map_zero])))
  rw [finsum_log_gaussNorm_mul h₁ h₂]
  simp_rw [hmah]
  rw [← mul_add]
  congr 1
  have hs : ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f₁.map σ) + mahler (H.normAt σ) k (f₂.map σ) +
      (k : ℝ) * ((δ₁ + δ₂ : ℕ) : ℝ) * (harmonic (n - 1) : ℝ) / 2) =
      ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f₁.map σ) + (k : ℝ) * δ₁ * (harmonic (n - 1) : ℝ) / 2) +
      ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f₂.map σ) + (k : ℝ) * δ₂ * (harmonic (n - 1) : ℝ) / 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    push_cast
    ring
  rw [hs]
  ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

section Lemmas

variable {R : Type*} [CommRing R]

theorem IsWeightedHomogeneous.bind₁ {σ τ : Type*} {w : σ → ℕ} {w' : τ → ℕ} {f : MvPolynomial σ R}
    {m : ℕ} (hf : IsWeightedHomogeneous w f m) (φ : σ → MvPolynomial τ R)
    (hφ : ∀ x, IsWeightedHomogeneous w' (φ x) (w x)) :
    IsWeightedHomogeneous w' (bind₁ φ f) m := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro d hd
  rw [bind₁_monomial]
  have hw : Finsupp.weight w d = m := hf (mem_support_iff.mp hd)
  have h1 : IsWeightedHomogeneous w' (∏ x ∈ d.support, φ x ^ d x) (∑ x ∈ d.support, d x * w x) :=
    IsWeightedHomogeneous.prod _ _ _ fun x _ => by
      simpa [mul_comm] using (hφ x).pow (d x)
  have h2 := h1.C_mul (AddMonoidAlgebra.coeff f d)
  convert h2 using 1
  rw [← hw, Finsupp.weight_apply, Finsupp.sum]
  simp [smul_eq_mul]

variable {k n : ℕ}

theorem IsMultiHomog.specFirst {δ : ℕ} {f : MvPolynomial (Fin (k + 1) × Fin n) R}
    (hf : IsMultiHomog δ f) (u : Fin n → R) : IsMultiHomog δ (specFirst f u) := by
  rw [isMultiHomog_iff] at hf ⊢
  intro i
  refine IsWeightedHomogeneous.bind₁ (hf i.succ) _ fun x => ?_
  obtain ⟨a, j⟩ := x
  induction a using Fin.cases with
  | zero =>
    have : inGroup (n := n) i.succ ((0 : Fin (k + 1)), j) = 0 := by
      simp [inGroup, (Fin.succ_ne_zero i).symm]
    rw [this]
    exact isWeightedHomogeneous_C _ _
  | succ a =>
    have : inGroup (n := n) i.succ (a.succ, j) = inGroup (n := n) i (a, j) := by
      simp [inGroup, Fin.succ_inj]
    rw [this]
    exact isWeightedHomogeneous_X R _ (a, j)

theorem IsWeightedHomogeneous.map' {σ S : Type*} [CommSemiring S] {w : σ → ℕ} {f : MvPolynomial σ R}
    {m : ℕ} (hf : IsWeightedHomogeneous w f m) (φ : R →+* S) :
    IsWeightedHomogeneous w (MvPolynomial.map φ f) m := by
  intro d hd
  rw [coeff_map] at hd
  exact hf fun h => hd (by rw [h, map_zero])

end Lemmas

section Components

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type*} [CommRing R] {n : ℕ}

theorem isHomogIdeal_iff (I : Ideal (MvPolynomial (Fin n) R)) :
    IsHomogIdeal I ↔ I.IsHomogeneous (homogeneousSubmodule (Fin n) R) := by
  constructor
  · intro h i r hr
    have := h r hr i
    rwa [← decomposition.decompose'_apply] at this
  · intro h f hf d
    exact homogeneousComponent_mem_of_mem h hf d

theorem isHomogIdeal_sup_span_linForm {I : Ideal (MvPolynomial (Fin n) R)} (hI : IsHomogIdeal I)
    (u : Fin n → R) : IsHomogIdeal (I ⊔ Ideal.span {linForm u}) := by
  rw [isHomogIdeal_iff] at hI ⊢
  refine hI.sup (Ideal.homogeneous_span _ _ fun x hx => ?_)
  rw [Set.mem_singleton_iff] at hx
  subst hx
  refine ⟨1, ?_⟩
  rw [mem_homogeneousSubmodule]
  exact IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _

variable [IsNoetherianRing R]

theorem isProjPrime_of_mem_support_fundCycle {J : Ideal (MvPolynomial (Fin n) R)} (hJ : IsHomogIdeal J)
    {W : Ideal (MvPolynomial (Fin n) R)} (hW : W ∈ (fundCycle J).support) : IsProjPrime W := by
  classical
  have hval : (fundCycle J) W ≠ 0 := Finsupp.mem_support_iff.mp hW
  have hrel : W ∈ relComps J := by
    by_contra h
    apply hval
    unfold fundCycle
    rw [Finsupp.onFinset_apply, if_neg h]
  obtain ⟨hmin, hW'⟩ := hrel
  have hprime : W.IsPrime := hmin.1.1
  have hJh := (isHomogIdeal_iff J).mp hJ
  refine ⟨hprime, (isHomogIdeal_iff W).mpr ?_, hW'⟩
  set core := (W.homogeneousCore (homogeneousSubmodule (Fin n) R)).toIdeal
  have hcore_prime : core.IsPrime := hprime.homogeneousCore
  have hJcore : J ≤ core := by
    rw [← hJh.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hmin.1.2
  have hle : core ≤ W := Ideal.toIdeal_homogeneousCore_le _ _
  have heq : core = W := le_antisymm hle (hmin.2 ⟨hcore_prime, hJcore⟩ hle)
  rw [Ideal.IsHomogeneous.iff_eq]
  exact heq

end Components

section Height

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem chowHt_zero_groups (H : ArchData K n) (δ : ℕ) (g : MvPolynomial (Fin 0 × Fin n) K) :
    chowHt H 0 δ g = chowHt H 0 0 g := by
  simp [chowHt]

theorem chowHt_zero_groups_eq_zero (H : ArchData K n) (δ : ℕ) {g : MvPolynomial (Fin 0 × Fin n) K}
    (hg : g ≠ 0) : chowHt H 0 δ g = 0 := by
  rw [chowHt_zero_groups, eq_C_of_isEmpty g]
  rw [eq_C_of_isEmpty g] at hg
  exact chowHeightConst K n 0 H _ fun h => hg (by rw [h, map_zero])

theorem chowHt_pow (hMul : ChowHeightMul.Statement) (H : ArchData K n) {k : ℕ} (d : ℕ)
    {g : MvPolynomial (Fin k × Fin n) K} (hg : g ≠ 0) (m : ℕ) :
    chowHt H k (m * d) (g ^ m) = m * chowHt H k d g := by
  induction m with
  | zero =>
    rw [zero_mul, pow_zero, Nat.cast_zero, zero_mul, ← C_1]
    exact chowHeightConst K n k H 1 one_ne_zero
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul, hMul K n H k _ _ _ _ (pow_ne_zero _ hg) hg, ih]
    push_cast
    ring

theorem chowHt_C_mul_prod (hMul : ChowHeightMul.Statement) (H : ArchData K n) {k : ℕ} {ι : Type*}
    (s : Finset ι) (m d : ι → ℕ) (g : ι → MvPolynomial (Fin k × Fin n) K) (hg : ∀ i ∈ s, g i ≠ 0)
    {c : K} (hc : c ≠ 0) :
    chowHt H k (∑ i ∈ s, m i * d i) (C c * ∏ i ∈ s, g i ^ m i) =
      ∑ i ∈ s, (m i : ℝ) * chowHt H k (d i) (g i) := by
  classical
  have hP : ∀ t ⊆ s, ∏ i ∈ t, g i ^ m i ≠ 0 := fun t ht =>
    Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hg i (ht hi))
  have hprod : ∀ t ⊆ s, chowHt H k (∑ i ∈ t, m i * d i) (∏ i ∈ t, g i ^ m i) =
      ∑ i ∈ t, (m i : ℝ) * chowHt H k (d i) (g i) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.sum_empty, Finset.prod_empty, Finset.sum_empty, ← C_1]
      exact chowHeightConst K n k H 1 one_ne_zero
    | insert a t ha ih =>
      intro hts
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
        hMul K n H k _ _ _ _ (pow_ne_zero _ (hg a (hts (Finset.mem_insert_self a t))))
          (hP t (fun x hx => hts (Finset.mem_insert_of_mem hx))),
        chowHt_pow hMul H _ (hg a (hts (Finset.mem_insert_self a t))),
        ih (fun x hx => hts (Finset.mem_insert_of_mem hx))]
  have := hMul K n H k 0 (∑ i ∈ s, m i * d i) (C c) _ (C_ne_zero.mpr hc) (hP s le_rfl)
  rw [zero_add] at this
  rw [this, chowHeightConst K n k H c hc, zero_add, hprod s le_rfl]



end Height


end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PClosedPointConeCoord
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

theorem aeval_cone_of_isHomogeneous {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {n d : ℕ}
    (y : Fin n → Ω) {p : MvPolynomial (Fin n) F} (hp : p.IsHomogeneous d) :
    aeval (fun j => Polynomial.C (y j) * Polynomial.X) p =
      Polynomial.C (aeval y p) * Polynomial.X ^ d := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ j ∈ m.support, m j = d := by
    have := hp (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, ← map_pow,
    ← map_prod, Polynomial.algebraMap_apply, map_mul, mul_assoc]

theorem ClosedPointConeCoord.proof : ClosedPointConeCoord.Statement := by
  intro F _ n I i hI hdim hXi Ω _ _ y hy hyI
  classical
  let φ : MvPolynomial (Fin n) F →ₐ[F] Polynomial Ω :=
    aeval fun j => Polynomial.C (y j) * Polynomial.X
  let P : Ideal (MvPolynomial (Fin n) F) := RingHom.ker φ
  have hPprime : P.IsPrime := RingHom.ker_isPrime _
  have hIP : I ≤ P := by
    intro g hg
    show φ g = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← sum_homogeneousComponent g, map_sum]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [show φ (homogeneousComponent d g) = _ from
      aeval_cone_of_isHomogeneous y (homogeneousComponent_isHomogeneous d g),
      hyI _ (hI.isHomog g hg d), map_zero, zero_mul]
  let m : Ideal (MvPolynomial (Fin n) F) := RingHom.ker (constantCoeff : MvPolynomial (Fin n) F →+* F)
  have hmprime : m.IsPrime := RingHom.ker_isPrime _
  have key : (Polynomial.evalRingHom (0 : Ω)).comp (φ : MvPolynomial (Fin n) F →+* Polynomial Ω) =
      (algebraMap F Ω).comp constantCoeff := by
    apply MvPolynomial.ringHom_ext <;> intro <;> simp [φ]
  have hPm : P ≤ m := by
    intro g hg
    have hg' : φ g = 0 := hg
    have h0 := RingHom.congr_fun key g
    simp only [RingHom.comp_apply, RingHom.coe_coe, hg', map_zero] at h0
    show constantCoeff g = 0
    exact (algebraMap F Ω).injective (by rw [← h0, map_zero])
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (funext h)
  have hXjP : X j ∉ P := by
    intro h
    have h' : φ (X j) = 0 := h
    simp only [φ, aeval_X] at h'
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hj) Polynomial.X_ne_zero h'
  have hXjm : X j ∈ m := by
    show constantCoeff (X j : MvPolynomial (Fin n) F) = 0
    simp
  have hPlt : P < m := lt_of_le_of_ne hPm fun h => hXjP (h ▸ hXjm)
  have hIeq : I = P := by
    by_contra hne
    have hIlt : I < P := lt_of_le_of_ne hIP hne
    have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ I) := by
      rw [ringKrullDim_quotient, Order.le_krullDim_iff]
      let a : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) F) I :=
        ⟨⟨I, hI.isPrime⟩, fun _ h => h⟩
      let b : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) F) I :=
        ⟨⟨P, hPprime⟩, fun _ h => hIP h⟩
      let c : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) F) I :=
        ⟨⟨m, hmprime⟩, fun _ h => hPm (hIP h)⟩
      have hab : a < b := hIlt
      have hbc : b < c := hPlt
      exact ⟨LTSeries.mk 2 ![a, b, c]
        (Fin.strictMono_iff_lt_succ.mpr fun k => by fin_cases k; exacts [hab, hbc]), rfl⟩
    rw [hdim] at h2
    norm_num at h2
  intro hyi
  apply hXi
  rw [hIeq]
  show φ (X i) = 0
  simp [φ, hyi]

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartChoiceAlgClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartChoiceAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (q : MvPolynomial (Fin e × Fin n) F),
    IsProjPrime I → IsChowForm I (e + 1) f → Prime q → ∃ t : Fin n → F, ¬ q ∣ specFirst f t

end

end GroundTheory.Heights₂.Heights
end

