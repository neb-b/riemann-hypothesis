module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartChoiceAlgClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartChoiceAlgClosed

variable {F : Type} [Field F] {n e : ℕ}

theorem isChowForm_iff_span {P : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {g : MvPolynomial (Fin k × Fin n) F} :
    IsChowForm P k g ↔ g ≠ 0 ∧ incIdeal P k = Ideal.span {g} := by
  have hmem : ∀ G : MvPolynomial (Fin k × Fin n) F,
      G ∈ incIdeal P k ↔ ∀ v ∈ incidence P k, aeval v G = 0 := fun G => by
    simp [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_⟩
    ext G
    rw [hmem, Ideal.mem_span_singleton]
    exact h G
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun G => ?_⟩
    rw [← hmem, h, Ideal.mem_span_singleton]

def shiftVar (e n : ℕ) : Fin e × Fin n → Fin (e + 1) × Fin n := fun jm => (jm.1.succ, jm.2)

def splitFirst (F : Type) [Field F] (e n : ℕ) :
    MvPolynomial (Fin (e + 1) × Fin n) F →ₐ[F] MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) :=
  aeval fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
    (X ij.2) (fun j => C (X (j, ij.2))) ij.1

def joinFirst (F : Type) [Field F] (e n : ℕ) :
    MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) →+* MvPolynomial (Fin (e + 1) × Fin n) F :=
  eval₂Hom (rename (shiftVar e n)).toRingHom (fun m => X (0, m))

theorem joinFirst_splitFirst (p : MvPolynomial (Fin (e + 1) × Fin n) F) :
    joinFirst F e n (splitFirst F e n p) = p := by
  have h : (joinFirst F e n).comp (splitFirst F e n).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [joinFirst, splitFirst, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, m⟩
      induction i using Fin.cases <;> simp [joinFirst, splitFirst, shiftVar]
  exact RingHom.congr_fun h p

theorem joinFirst_C (a : MvPolynomial (Fin e × Fin n) F) :
    joinFirst F e n (C a) = rename (shiftVar e n) a := by
  simp [joinFirst]

theorem specFirst_rename_shiftVar (q : MvPolynomial (Fin e × Fin n) F) :
    specFirst (rename (shiftVar e n) q) 0 = q := by
  unfold specFirst
  rw [bind₁_rename]
  have : (specFirstVar (0 : Fin n → F) ∘ shiftVar e n) = X := by
    funext jm
    simp [specFirstVar, shiftVar]
  rw [this, bind₁_X_left]
  rfl

theorem specFirst_zero_of_isMultiHomog {δ : ℕ} (hδ : 1 ≤ δ) {f : MvPolynomial (Fin (e + 1) × Fin n) F}
    (hf : IsMultiHomog δ f) : specFirst f 0 = 0 := by
  classical
  unfold specFirst
  conv_lhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [bind₁_monomial]
  obtain ⟨i, hi, h0⟩ : ∃ i ∈ s.support, i.1 = 0 := by
    by_contra hno
    push Not at hno
    have hw := congrFun (hf (mem_support_iff.mp hs)) 0
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at hw
    have : ∑ c ∈ s.support, (s c • groupWeight (e + 1) n c) 0 = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      simp [groupWeight, Ne.symm (hno c hc)]
    omega
  rw [Finset.prod_eq_zero hi, mul_zero]
  obtain ⟨a, m⟩ := i
  simp only at h0
  subst h0
  simp [specFirstVar, zero_pow (Finsupp.mem_support_iff.mp hi)]

theorem eval_map_splitFirst (J : Ideal (MvPolynomial (Fin e × Fin n) F)) (t : Fin n → F)
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) :
    eval (fun m => Ideal.Quotient.mk J (C (t m))) (map (Ideal.Quotient.mk J) (splitFirst F e n f)) =
      Ideal.Quotient.mk J (specFirst f t) := by
  rw [eval_map]
  have h : (eval₂Hom (Ideal.Quotient.mk J) (fun m => Ideal.Quotient.mk J (C (t m)))).comp
      (splitFirst F e n).toRingHom = (Ideal.Quotient.mk J).comp (bind₁ (specFirstVar t)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [splitFirst, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, m⟩
      induction i using Fin.cases <;> simp [splitFirst, specFirstVar]
  exact RingHom.congr_fun h f

end ChartChoiceAlgClosed


open ChartChoiceAlgClosed in
theorem ChartChoiceAlgClosed.proof (h₁ : IncIdealPrime.Statement) (h₂ : ChowFormMultiHomog.Statement) :
    ChartChoiceAlgClosed.Statement := by
  intro F _ _ n e I f q hI hf hq
  classical
  obtain ⟨hf0, hspan⟩ := isChowForm_iff_span.mp hf
  have hfp : Prime f := by
    have := h₁ F n (e + 1) I hI.isPrime hI.isRelevant
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hf0).mp this
  obtain ⟨δ, hδ, hhom⟩ := h₂ F n (e + 1) I f hI hf

  have hndvd : ¬ rename (shiftVar e n) q ∣ f := by
    rintro ⟨g, hg⟩
    rcases hfp.2.2 (rename (shiftVar e n) q) g (hg ▸ dvd_refl f) with ⟨h, hh⟩ | ⟨h, hh⟩
    · have := congrArg (fun p => specFirst p 0) hh
      rw [specFirst_rename_shiftVar] at this
      unfold specFirst at this
      rw [map_mul] at this
      have h0 : specFirst f 0 = 0 := specFirst_zero_of_isMultiHomog hδ hhom
      unfold specFirst at h0
      rw [h0, zero_mul] at this
      exact hq.ne_zero this
    · have hunit : IsUnit (rename (shiftVar e n) q) := by
        refine isUnit_iff_exists_inv.mpr ⟨h, ?_⟩
        apply mul_left_cancel₀ hf0
        calc f * (rename (shiftVar e n) q * h) = rename (shiftVar e n) q * (f * h) := by ring
          _ = f * 1 := by rw [← hh, ← hg, mul_one]
      have := hunit.map (bind₁ (specFirstVar (0 : Fin n → F)))
      have h' : bind₁ (specFirstVar (0 : Fin n → F)) (rename (shiftVar e n) q) = q :=
        specFirst_rename_shiftVar q
      rw [h'] at this
      exact hq.not_isUnit this
  set J : Ideal (MvPolynomial (Fin e × Fin n) F) := Ideal.span {q} with hJ
  have : J.IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  set P := map (Ideal.Quotient.mk J) (splitFirst F e n f) with hP
  have hP0 : P ≠ 0 := by
    intro h0
    have hmem : splitFirst F e n f ∈ RingHom.ker (map (σ := Fin n) (Ideal.Quotient.mk J)) := by
      rw [RingHom.mem_ker]; exact h0
    rw [MvPolynomial.ker_map, Ideal.mk_ker, hJ, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton] at hmem
    apply hndvd
    have := map_dvd (joinFirst F e n) hmem
    rwa [joinFirst_splitFirst, joinFirst_C] at this

  let g : ℕ ↪ F := Infinite.natEmbedding F
  have hinj : Function.Injective fun k : ℕ => Ideal.Quotient.mk J (C (g k)) := by
    intro a b hab
    apply g.injective
    apply (algebraMap F (MvPolynomial (Fin e × Fin n) F ⧸ J)).injective
    exact hab
  by_contra hall
  push Not at hall
  apply hP0
  refine eq_zero_of_eval_zero_at_prod_finset P
    (fun _ => (Finset.range (P.totalDegree + 1)).image (fun k : ℕ => Ideal.Quotient.mk J (C (g k))))
    (fun i => ?_) (fun x hx => ?_)
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    exact Nat.lt_succ_of_le (degreeOf_le_totalDegree P i)
  · choose k _ hk using fun i => Finset.mem_image.mp (hx i)
    have hx' : x = fun m => Ideal.Quotient.mk J (C ((fun m => g (k m)) m)) := by
      funext m
      rw [← hk m]
    rw [hx', hP, eval_map_splitFirst]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hall _))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormAssoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ChowFormAssoc.proof : ChowFormAssoc.Statement := by
  intro F _ n k I g g' hg hg'
  have h1 : g ∣ g' := (hg.2 g').mp ((hg'.2 g').mpr dvd_rfl)
  have h2 : g' ∣ g := (hg'.2 g).mp ((hg.2 g).mpr dvd_rfl)
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd h1 h2
  obtain ⟨c, hc, hcu⟩ :=
    (isUnit_iff_eq_C_of_isReduced (P := (u : MvPolynomial (Fin k × Fin n) F))).mp u.isUnit
  refine ⟨c, hc.ne_zero, ?_⟩
  rw [← hu, hcu, mul_comm]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormBaseChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isHomogIdeal_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (φ : R →+* S)
    {I : Ideal (MvPolynomial (Fin n) R)} (hI : IsHomogIdeal I) :
    IsHomogIdeal (I.map (MvPolynomial.map φ)) := by
  rw [isHomogIdeal_iff] at hI ⊢
  obtain ⟨T, hT⟩ := (Ideal.IsHomogeneous.iff_exists _ _).mp hI
  rw [hT, Ideal.map_span]
  refine Ideal.homogeneous_span _ _ ?_
  rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
  obtain ⟨d, hd⟩ := x.2
  refine ⟨d, ?_⟩
  rw [mem_homogeneousSubmodule] at hd ⊢
  exact hd.map φ

theorem ChowFormBaseChange.proof (hRad : RadicalBaseChange.Statement)
    (hExt : ChowFormExtend.Statement) (hRed : ChowFormReduced.Statement) :
    ChowFormBaseChange.Statement := by
  intro K _ _ n k I f σ hI hf
  have hJ : IsHomogIdeal (I.map (MvPolynomial.map σ)) := isHomogIdeal_map σ hI.isHomog
  refine ⟨fun W hW => isProjPrime_of_mem_support_fundCycle hJ hW, ?_⟩
  exact hRed ℂ n k _ _ hJ (hRad K ℂ σ (Fin n) I hI.isPrime.isRadical) (hExt K ℂ σ n k I f hf)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormCycleAdd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ChowFormCycleAdd.proof (h1 : ChowFormAssoc.Statement) : ChowFormCycleAdd.Statement := by
  classical
  intro F _ n k Z₁ Z₂ f₁ f₂ ⟨c₁, hc₁, g₁, hg₁, hf₁⟩ ⟨c₂, hc₂, g₂, hg₂, hf₂⟩
  subst hf₁ hf₂
  let g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin k × Fin n) F :=
    fun W => if W ∈ Z₁.support then g₁ W else g₂ W
  have hd : ∀ W, ∃ d : F, d ≠ 0 ∧ (W ∈ Z₂.support → g₂ W = C d * g W) := by
    intro W
    by_cases hW1 : W ∈ Z₁.support
    · by_cases hW2 : W ∈ Z₂.support
      · obtain ⟨d, hd, he⟩ := h1 F n k W (g₁ W) (g₂ W) (hg₁ W hW1) (hg₂ W hW2)
        exact ⟨d, hd, fun _ => by simp only [g, if_pos hW1, he]⟩
      · exact ⟨1, one_ne_zero, fun h => absurd h hW2⟩
    · exact ⟨1, one_ne_zero, fun _ => by simp only [g, if_neg hW1, map_one, one_mul]⟩
  choose d hd0 hdg using hd
  have hsupp : (Z₁ + Z₂).support = Z₁.support ∪ Z₂.support := by
    ext W
    simp only [Finsupp.mem_support_iff, Finset.mem_union, Finsupp.coe_add, Pi.add_apply, ne_eq,
      Nat.add_eq_zero_iff, not_and_or]
  refine ⟨c₁ * c₂ * ∏ W ∈ Z₂.support, d W ^ Z₂ W, ?_, g, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero hc₁ hc₂)
      (Finset.prod_ne_zero_iff.mpr fun W _ => pow_ne_zero _ (hd0 W))
  · intro W hW
    rw [hsupp, Finset.mem_union] at hW
    by_cases hW1 : W ∈ Z₁.support
    · simpa only [g, if_pos hW1] using hg₁ W hW1
    · simpa only [g, if_neg hW1] using hg₂ W (hW.resolve_left hW1)
  · have e1 : ∏ W ∈ Z₁.support, g₁ W ^ Z₁ W =
        ∏ W ∈ Z₁.support ∪ Z₂.support, g W ^ Z₁ W := by
      rw [← Finset.prod_subset Finset.subset_union_left (f := fun W => g W ^ Z₁ W)]
      · exact Finset.prod_congr rfl fun W hW => by simp only [g, if_pos hW]
      · intro W _ hW
        rw [Finsupp.mem_support_iff, not_not] at hW
        simp [hW]
    have e2 : ∏ W ∈ Z₂.support, g₂ W ^ Z₂ W =
        C (∏ W ∈ Z₂.support, d W ^ Z₂ W) * ∏ W ∈ Z₁.support ∪ Z₂.support, g W ^ Z₂ W := by
      rw [← Finset.prod_subset Finset.subset_union_right (f := fun W => g W ^ Z₂ W)]
      · rw [map_prod, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun W hW => by rw [hdg W hW, mul_pow, map_pow]
      · intro W _ hW
        rw [Finsupp.mem_support_iff, not_not] at hW
        simp [hW]
    rw [hsupp, e1, e2]
    simp only [Finsupp.coe_add, Pi.add_apply, pow_add, Finset.prod_mul_distrib, map_mul]
    ring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormCycleSmul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ChowFormCycleSmul.proof : ChowFormCycleSmul.Statement := by
  intro F _ n k m Z f hZ
  obtain ⟨c, hc, g, hg, hf⟩ := hZ
  refine ⟨c ^ m, pow_ne_zero _ hc, g, fun W hW => hg W (Finsupp.support_smul hW), ?_⟩
  have hsub : (m • Z).support ⊆ Z.support := Finsupp.support_smul
  rw [Finset.prod_subset hsub (fun W _ hW => by rw [Finsupp.notMem_support_iff.mp hW, pow_zero]), hf,
    mul_pow, ← map_pow, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun W _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, ← pow_mul, mul_comm]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormReduced
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Helpers

variable {F : Type*} [Field F] {n k : ℕ}

theorem incidence_mono {I W : Ideal (MvPolynomial (Fin n) F)} (hIW : I ≤ W)
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence W k) : u ∈ incidence I k := by
  obtain ⟨x, hx0, hxW, hxu⟩ := hu
  exact ⟨x, hx0, fun g hg => hxW g (hIW hg), hxu⟩

theorem exists_relComps_of_mem_incidence {J : Ideal (MvPolynomial (Fin n) F)}
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence J k) :
    ∃ W ∈ relComps J, u ∈ incidence W k := by
  obtain ⟨x, hx0, hxJ, hxu⟩ := hu
  let φ : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F := aeval x
  have hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have hJP : J ≤ RingHom.ker φ := fun g hg => RingHom.mem_ker.mpr (hxJ g hg)
  obtain ⟨W, hW, hWP⟩ := Ideal.exists_minimalPrimes_le hJP
  refine ⟨W, ⟨hW, ?_⟩, x, hx0, fun g hg => RingHom.mem_ker.mp (hWP hg), hxu⟩
  by_contra hrel
  apply hx0
  funext j
  have hj : X j ∈ W := by
    by_contra hj
    exact hrel ⟨j, hj⟩
  have := RingHom.mem_ker.mp (hWP hj)
  simpa [φ] using this

theorem mem_support_fundCycle_iff {J : Ideal (MvPolynomial (Fin n) F)} (hJ : J.IsRadical)
    {W : Ideal (MvPolynomial (Fin n) F)} : W ∈ (fundCycle J).support ↔ W ∈ relComps J := by
  classical
  rw [Finsupp.mem_support_iff]
  unfold fundCycle
  rw [Finsupp.onFinset_apply]
  constructor
  · intro h
    by_contra h'
    exact h (if_neg h')
  · intro h
    rw [if_pos h, localMult_eq_one_of_isRadical hJ h.1]
    exact one_ne_zero

end Helpers

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeAverage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem ConeAverage.proof (h1 : ConeIntegralMass.Statement) (h2 : ChowDegreePos.Statement)
    (h3 : ConeFubini.Statement) (h4 : FsLogAverage.Statement) (h5 : FsLogMeasurable.Statement) :
    ConeAverage.Statement := by
  intro n e δ h W g hW hg hδ
  set S : Set (EuclideanSpace ℂ (Fin n)) :=
    {y | ‖y‖ < 1 ∧ ∀ q ∈ W, eval (h.pointOf y) q = 0} with hS
  set ν : Measure (EuclideanSpace ℂ (Fin n)) := Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) with hν
  set D : ℝ := (ν {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}).toReal
    with hD
  have hδ1 : 1 ≤ δ := h2 n (e + 1) δ W g (Nat.succ_pos e) hW hg hδ
  have hmass : (ν S).toReal / D = δ := by
    have hm := h1 n e δ h W g hW hg hδ
    unfold coneIntegral at hm
    rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_one] at hm
    exact hm
  have hfin : ν S ≠ ⊤ := by
    intro hinf
    rw [hinf, ENNReal.toReal_top, zero_div] at hmass
    have : (δ : ℝ) ≠ 0 := by exact_mod_cast (by omega : δ ≠ 0)
    exact this hmass.symm
  have : IsFiniteMeasure (ν.restrict S) := isFiniteMeasure_restrict.2 hfin
  have hcone : ∀ φ : (Fin n → ℂ) → ℝ,
      coneIntegral h W e φ = (∫ y, φ (h.pointOf y) ∂(ν.restrict S)) / D := fun _ => rfl
  have hzero : ν.restrict S {(0 : EuclideanSpace ℂ (Fin n))} = 0 := by
    refine nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le S _).trans_eq ?_)
    have hd : (((2 * (e + 1) : ℕ) : ℝ)) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) := by simp
    rw [hν, hd]
    apply hausdorffMeasure_of_dimH_lt
    rw [dimH_singleton]
    exact_mod_cast (by omega : 0 < 2 * (e + 1))
  have hae : ∀ᵐ y ∂(ν.restrict S), y ≠ 0 := by
    rw [ae_iff]
    simpa using hzero
  have hF := h3 n h (ν.restrict S) (fun v y => fsLog h (nrmv h v) (h.pointOf y))
    (-(harmonic (n - 1) : ℝ) / 2)
    ((harmonic (n - 1) : ℝ) / 2 * (volume (ballH h)).toReal) (h5 n h)
    (hae.mono fun y hy => by
      obtain ⟨hi, habs, hmean⟩ := h4 n h y hy
      exact ⟨hi, habs.le, hmean⟩)
  obtain ⟨hFi, hFm⟩ := hF
  have hfun : (fun v => coneIntegral h W e (fsLog h (nrmv h v))) =
      fun v => (∫ y, fsLog h (nrmv h v) (h.pointOf y) ∂(ν.restrict S)) / D := by
    funext v
    exact hcone _
  rw [hfun]
  refine ⟨hFi.div_const D, ?_⟩
  rw [setAverage_eq, integral_div, ← smul_div_assoc, ← setAverage_eq, hFm,
    Measure.restrict_apply_univ, mul_div_assoc, hmass]
  ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDivCyclePrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

theorem isHomogeneous_of_mem_minimalPrimes {I P : Ideal (MvPolynomial (Fin n) ℂ)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ)) (hP : P ∈ I.minimalPrimes) :
    P.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) := by
  have hcore : (P.homogeneousCore (homogeneousSubmodule (Fin n) ℂ)).toIdeal.IsPrime :=
    hP.1.1.homogeneousCore
  have hle : I ≤ (P.homogeneousCore (homogeneousSubmodule (Fin n) ℂ)).toIdeal :=
    hI.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hP.1.2)
  have hcoreP := Ideal.toIdeal_homogeneousCore_le (homogeneousSubmodule (Fin n) ℂ) P
  rw [Ideal.IsHomogeneous.iff_eq]
  exact le_antisymm hcoreP (hP.2 ⟨hcore, hle⟩ hcoreP)

end GroundTheory.Heights₂.Heights
end

