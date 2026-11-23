module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0008

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChartDomain
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace ChartDomain

variable {D : Type} [CommRing D] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)

abbrev Base : Type := Localization.Away (Ideal.Quotient.mk Q (X j))

def cx (e : ℕ) (l : Fin n) : MvPolynomial (Par e n) (Base Q j) :=
  C (algebraMap _ _ (Ideal.Quotient.mk Q (X l)))

def cinv (e : ℕ) : MvPolynomial (Par e n) (Base Q j) :=
  C (IsLocalization.Away.invSelf (Ideal.Quotient.mk Q (X j)))

theorem cx_mul_cinv : cx Q j e j * cinv Q j e = 1 := by
  rw [cx, cinv, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]

def parVal : Par e n → MvPolynomial (Par e n) (Base Q j)
  | .inl (i, l) => X (.inl (i, l)) -
      if l = j then cinv Q j e * ∑ m, X (.inl (i, m)) * cx Q j e m else 0
  | .inr l => X (.inr l) -
      if l = j then cinv Q j e * (∑ m, X (.inr m) * cx Q j e m - 1) else 0

def κ (e : ℕ) : D →+* MvPolynomial (Par e n) (Base Q j) :=
  (C : Base Q j →+* _).comp ((algebraMap _ (Base Q j)).comp ((Ideal.Quotient.mk Q).comp C))

def evalF (e : ℕ) :
    MvPolynomial (Fin n) (MvPolynomial (Par e n) D) →+* MvPolynomial (Par e n) (Base Q j) :=
  eval₂Hom (eval₂Hom (κ Q j e) (parVal Q j)) (cx Q j e)

theorem evalF_comp_map :
    (evalF Q j e).comp (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D)) =
      (C : Base Q j →+* _).comp ((algebraMap _ (Base Q j)).comp (Ideal.Quotient.mk Q)) := by
  apply MvPolynomial.ringHom_ext
  · intro d; simp [evalF, κ]
  · intro l; simp [evalF, cx]

theorem secIdeal_le_ker :
    secIdeal (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) X ≤ RingHom.ker (evalF Q j e) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro q hq
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, evalF_comp_map]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hq]
  · rw [Ideal.span_le, Set.range_subset_iff]
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [SetLike.mem_coe, RingHom.mem_ker, secForm, linForm, map_sum, map_mul]
    simp only [evalF, coe_eval₂Hom, eval₂_C, eval₂Hom_X', parVal]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    linear_combination (-(∑ m, X (.inl (i, m)) * cx Q j e m)) * cx_mul_cinv Q j (e := e)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [SetLike.mem_coe, RingHom.mem_ker, chartForm, linForm, map_sub, map_one, map_sum, map_mul]
    simp only [evalF, coe_eval₂Hom, eval₂_C, eval₂Hom_X', parVal]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    linear_combination (-(∑ m, X (.inr m) * cx Q j e m - 1)) * cx_mul_cinv Q j (e := e)

abbrev secI (e : ℕ) : Ideal (MvPolynomial (Fin n) (MvPolynomial (Par e n) D)) :=
  secIdeal (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) (X : Par e n → MvPolynomial (Par e n) D)

abbrev Sec (e : ℕ) : Type :=
  SecAlg (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) (X : Par e n → MvPolynomial (Par e n) D)

abbrev xj (e : ℕ) : Sec Q e :=
  secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) (X : Par e n → MvPolynomial (Par e n) D) j

abbrev Chart (e : ℕ) : Type :=
  Localization.Away (secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D)))
    (X : Par e n → MvPolynomial (Par e n) D) j)

def toChart (e : ℕ) : MvPolynomial (Fin n) (MvPolynomial (Par e n) D) →+* Chart Q j e :=
  algebraMap _ (Chart Q j e)

theorem toChart_apply (e : ℕ) (a : MvPolynomial (Fin n) (MvPolynomial (Par e n) D)) :
    toChart Q j e a =
      algebraMap (Sec Q e) (Chart Q j e) (Ideal.Quotient.mk (secI Q e) a) := rfl

def toPoly (e : ℕ) : Chart Q j e →+* MvPolynomial (Par e n) (Base Q j) :=
  IsLocalization.Away.lift (xj Q j e)
    (g := Ideal.Quotient.lift (secI Q e) (evalF Q j e) (fun _ ha => RingHom.mem_ker.mp (secIdeal_le_ker Q j ha))) (by
      simp only [xj, secCoord, Ideal.Quotient.lift_mk, evalF, coe_eval₂Hom, eval₂_X]
      exact IsUnit.of_mul_eq_one _ (cx_mul_cinv Q j (e := e)))

theorem toPoly_toChart (e : ℕ) (a : MvPolynomial (Fin n) (MvPolynomial (Par e n) D)) :
    toPoly Q j e (toChart Q j e a) = evalF Q j e a := by
  rw [toChart_apply, toPoly, IsLocalization.Away.lift_eq, Ideal.Quotient.lift_mk]

theorem toChart_eq_zero {e : ℕ} {a : MvPolynomial (Fin n) (MvPolynomial (Par e n) D)} (ha : a ∈ secI Q e) :
    toChart Q j e a = 0 := by
  rw [toChart_apply, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

def quotToChart (e : ℕ) : MvPolynomial (Fin n) D ⧸ Q →+* Chart Q j e :=
  Ideal.Quotient.lift Q ((toChart Q j e).comp (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D)))
    (fun _ hq => toChart_eq_zero Q j (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hq))))

def baseToChart (e : ℕ) : Base Q j →+* Chart Q j e :=
  IsLocalization.Away.lift (Ideal.Quotient.mk Q (X j)) (g := quotToChart Q j e) (by
    rw [quotToChart, Ideal.Quotient.lift_mk, RingHom.comp_apply, map_X, toChart_apply]
    exact IsLocalization.Away.algebraMap_isUnit (xj Q j e))

def fromPoly (e : ℕ) : MvPolynomial (Par e n) (Base Q j) →+* Chart Q j e :=
  eval₂Hom (baseToChart Q j e) fun p => toChart Q j e (C (X p))

theorem baseToChart_mk (p : MvPolynomial (Fin n) D) :
    baseToChart Q j e (algebraMap _ (Base Q j) (Ideal.Quotient.mk Q p)) =
      toChart Q j e (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D) p) := by
  rw [baseToChart, IsLocalization.Away.lift_eq, quotToChart, Ideal.Quotient.lift_mk, RingHom.comp_apply]

theorem fromPoly_cx (l : Fin n) : fromPoly Q j e (cx Q j e l) = toChart Q j e (X l) := by
  rw [cx, fromPoly, coe_eval₂Hom, eval₂_C, baseToChart_mk, map_X]

theorem fromPoly_X (p : Par e n) : fromPoly Q j e (X p) = toChart Q j e (C (X p)) := by
  rw [fromPoly, coe_eval₂Hom, eval₂_X]

theorem fromPoly_secForm (i : Fin e) :
    fromPoly Q j e (∑ m, X (.inl (i, m)) * cx Q j e m) = 0 := by
  have hmem : secForm (X : Par e n → MvPolynomial (Par e n) D) i ∈ secI Q e :=
    Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
  rw [← toChart_eq_zero Q j hmem]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, fromPoly_X, fromPoly_cx, secForm, linForm]

theorem fromPoly_chartForm :
    fromPoly Q j e (∑ m, X (.inr m) * cx Q j e m - 1) = 0 := by
  have hmem : chartForm (X : Par e n → MvPolynomial (Par e n) D) - 1 ∈ secI Q e :=
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  rw [← toChart_eq_zero Q j hmem]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_sub, map_one, fromPoly_X, fromPoly_cx, chartForm, linForm]

theorem fromPoly_toPoly_toChart :
    ((fromPoly Q j e).comp (toPoly Q j e)).comp (toChart Q j e) = toChart Q j e := by
  apply MvPolynomial.ringHom_ext
  · intro c
    have h : (((fromPoly Q j e).comp (toPoly Q j e)).comp (toChart Q j e)).comp C =
        (toChart Q j e).comp C := by
      apply MvPolynomial.ringHom_ext
      · intro d
        simp only [RingHom.comp_apply, toPoly_toChart, evalF, κ, coe_eval₂Hom, eval₂_C, fromPoly,
          baseToChart_mk, map_C]
      · intro p
        simp only [RingHom.comp_apply, toPoly_toChart, evalF, coe_eval₂Hom, eval₂_C, eval₂_X]
        rcases p with ⟨i, l⟩ | l
        · simp only [parVal, map_sub, fromPoly_X]
          split_ifs
          · rw [map_mul, fromPoly_secForm, mul_zero, sub_zero]
          · rw [map_zero, sub_zero]
        · simp only [parVal, map_sub, fromPoly_X]
          split_ifs
          · rw [map_mul, fromPoly_chartForm, mul_zero, sub_zero]
          · rw [map_zero, sub_zero]
    exact RingHom.congr_fun h c
  · intro l
    simp only [RingHom.comp_apply, toPoly_toChart, evalF, coe_eval₂Hom, eval₂_X, fromPoly_cx]

theorem fromPoly_comp_toPoly : (fromPoly Q j e).comp (toPoly Q j e) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (xj Q j e))
  apply Ideal.Quotient.ringHom_ext
  exact fromPoly_toPoly_toChart Q j

theorem toPoly_algebraMap (d : D) : toPoly Q j e (algebraMap D (Chart Q j e) d) = κ Q j e d := by
  rw [IsScalarTower.algebraMap_apply D (MvPolynomial (Fin n) (MvPolynomial (Par e n) D)) (Chart Q j e),
    MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  exact (toPoly_toChart Q j e _).trans (by simp [evalF])

end ChartDomain


open ChartDomain in
theorem ChartDomain.proof : ChartDomain.Statement := by
  intro D _ _ n e Q j hQ hQD hXj
  have hxj : Ideal.Quotient.mk Q (X j) ≠ 0 := fun h => hXj (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have : IsDomain (MvPolynomial (Fin n) D ⧸ Q) := Ideal.Quotient.isDomain Q
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hxj
  have : IsDomain (Base Q j) := IsLocalization.isDomain_localization hle
  have hinj : Function.Injective (toPoly Q j e) :=
    Function.LeftInverse.injective (g := fromPoly Q j e) fun x => RingHom.congr_fun (fromPoly_comp_toPoly Q j) x
  refine ⟨Function.Injective.isDomain _ hinj, ?_⟩
  intro a b hab
  have h := congrArg (toPoly Q j e) hab
  rw [toPoly_algebraMap, toPoly_algebraMap] at h
  have h2 := IsLocalization.injective (Base Q j) hle (C_injective _ _ h)
  have h3 : C (a - b) ∈ Q := by rw [map_sub]; exact Ideal.Quotient.eq.mp h2
  exact sub_eq_zero.mp (hQD _ h3)

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowFormHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

variable {F : Type} [Field F] {n k : ℕ}

theorem chowForm_degree_unique {I : Ideal (MvPolynomial (Fin n) F)}
    {f g : MvPolynomial (Fin k × Fin n) F} (hk : 0 < k) (hf : IsChowForm I k f)
    (hg : IsChowForm I k g) {δ δ' : ℕ} (hδ : IsMultiHomog δ f) (hδ' : IsMultiHomog δ' g) :
    δ = δ' := by
  obtain ⟨q, rfl⟩ : f ∣ g := (hf.2 g).mp ((hg.2 g).mpr dvd_rfl)
  obtain ⟨r, hr⟩ : f * q ∣ f := (hg.2 f).mp ((hf.2 f).mpr dvd_rfl)
  have hqr : q * r = 1 := by
    have h' : f * (q * r) = f * 1 := by
      rw [mul_one, ← mul_assoc]
      exact hr.symm
    exact mul_left_cancel₀ hf.1 h'
  obtain ⟨c, -, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := q)).mp (IsUnit.of_mul_eq_one r hqr)
  have h1 : IsWeightedHomogeneous (groupWeight k n) (f * C c) ((fun _ => δ) + 0) :=
    IsWeightedHomogeneous.mul hδ (isWeightedHomogeneous_C _ c)
  rw [add_zero] at h1
  exact congrFun (IsWeightedHomogeneous.inj_right hg.1 h1 hδ') ⟨0, hk⟩

theorem ChowFormHomog.proof : ChowFormHomog.Statement := by
  intro F _ n k I f hf
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    exact fun d _ => funext fun i => i.elim0
  choose a ha using fun i => hf.exists_isWeightedHomogeneous_inGroup i
  have hδ : IsMultiHomog (a ⟨0, hk⟩) f := (isMultiHomog_iff _ _).mpr fun i => by
    rw [hf.degrees_eq ha ⟨0, hk⟩ i]
    exact ha i
  have hdeg : chowDegree I k = a ⟨0, hk⟩ := by
    apply le_antisymm
    · exact Nat.sInf_le ⟨f, hf, hδ⟩
    · exact le_csInf ⟨_, f, hf, hδ⟩ fun δ ⟨g, hg, hδg⟩ =>
        (chowForm_degree_unique hk hf hg hδ hδg).le
  rw [hdeg]
  exact hδ

theorem chowFormHomog : ChowFormHomog.Statement := ChowFormHomog.proof

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowNormForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem specRest_map {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {n e : ℕ}
    (φ : R →+* S) (ψ : S →+* T) (f : MvPolynomial (Fin (e + 1) × Fin n) R) (y : Par e n → S) :
    (specRest φ f y).map ψ = specRest (ψ.comp φ) f (ψ ∘ y) := by
  unfold specRest
  rw [eval₂_comp_left]
  congr 1
  · exact RingHom.ext fun a => by simp
  · funext ij
    obtain ⟨i, j⟩ := ij
    refine Fin.cases ?_ (fun i => ?_) i <;> simp

theorem ChowNormForm.proof (h₁ : ChowNormFormGeneric.Statement)
    (h₂ : SecAlgFieldChange.Statement) : ChowNormForm.Statement := by
  intro k E _ _ _ _ n e Q g y hy hQ hg
  have hinj : Function.Injective
      ((MvPolynomial.aeval y : MvPolynomial (Par e n) k →ₐ[k] E) : MvPolynomial (Par e n) k →+* E) :=
    hy
  set φ : GenParField k e n →+* E := IsFractionRing.lift hinj with hφ
  have hφC : φ.comp (algebraMap k (GenParField k e n)) = algebraMap k E := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k (MvPolynomial (Par e n) k),
      hφ, IsFractionRing.lift_algebraMap]
    simp
  have hy' : y = φ ∘ genPar k e n := by
    funext p
    simp [hφ, genPar, IsFractionRing.lift_algebraMap]
  have hQ' : Q.map (MvPolynomial.map (algebraMap k E)) =
      (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))).map (MvPolynomial.map φ) := by
    rw [Ideal.map_map]
    congr 1
    exact RingHom.ext fun p => by rw [RingHom.comp_apply, map_map, hφC]
  obtain ⟨hfin₀, c, hc, heq⟩ := h₁ k n e Q g hQ hg
  obtain ⟨hfin, hnorm⟩ := h₂ (GenParField k e n) E φ n e _ (genPar k e n) hfin₀
  rw [hQ', hy']
  refine ⟨hfin, φ c, (map_ne_zero φ).mpr hc, ?_⟩
  rw [← hnorm, ← hφC, ← specRest_map, heq, _root_.map_mul, map_C]

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowNormFormGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem genPar_algebraicIndependent (k : Type*) [Field k] (e n : ℕ) :
    AlgebraicIndependent k (genPar k e n) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k)
      (GenParField k e n)) :=
    IsFractionRing.injective (MvPolynomial (Par e n) k) (GenParField k e n)
  have h := (MvPolynomial.algebraicIndependent_X (Par e n) k).map' hinj
  have hc : (⇑(IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k) (GenParField k e n)) ∘ X) =
      genPar k e n := by
    funext p
    simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', genPar]
  rwa [hc] at h

theorem secCoord_adjoin {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) : Algebra.adjoin E (Set.range (secCoord Q y)) = ⊤ := by
  have h : Set.range (secCoord Q y) = Set.range (Ideal.Quotient.mkₐ E (secIdeal Q y) ∘ X) := rfl
  rw [h, Set.range_comp, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top,
    AlgHom.range_eq_top]
  exact Ideal.Quotient.mkₐ_surjective E _

theorem secCoord_chart {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) : ∑ j, algebraMap E (SecAlg Q y) (y (.inr j)) * secCoord Q y j = 1 := by
  have h : Ideal.Quotient.mk (secIdeal Q y) (chartForm y) = 1 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h, chartForm, linForm, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  rfl

theorem ChowNormFormGeneric.proof (h₁ : SecAlgFinite.Statement) (h₂ : GenSecDomain.Statement)
    (h₃ : GenSecSeparable.Statement) (h₄ : ChowSecDvd.Statement)
    (h₅ : NormFormIrreducible.Statement) (h₆ : GenChowIrreducible.Statement)
    (h₇ : NormFormDvd.Statement) : ChowNormFormGeneric.Statement := by
  intro k _ _ n e Q g hQ hg
  have hfin := h₁ k (GenParField k e n) n e Q g (genPar k e n)
    (genPar_algebraicIndependent k e n) hQ hg
  refine ⟨hfin, ?_⟩
  have := h₂ k n e Q g hQ hg
  have := h₃ k n e Q g hQ hg
  have hirr := h₅ (GenParField k e n) (GenSec k e Q) n _ (fun j => genPar k e n (.inr j))
    (secCoord_adjoin _ _) (secCoord_chart _ _)
  obtain ⟨m, -, hm⟩ := h₄ k (GenParField k e n) n e Q g (genPar k e n) hQ hg
  have hd := h₇ (GenParField k e n) (GenSec k e Q) n _
    ((specRest (algebraMap k (GenParField k e n)) g (genPar k e n)) ^ m) (by rwa [map_pow])
  rw [← pow_mul] at hd
  obtain ⟨u, hu⟩ := hirr.prime.dvd_of_dvd_pow hd
  rcases (h₆ k n e Q g hQ hg).isUnit_or_isUnit hu with hN | hu'
  · exact absurd hN hirr.not_isUnit
  obtain ⟨c, hc, rfl⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp hu'
  exact ⟨c, hc.ne_zero, by rw [hu, mul_comm]⟩

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormDvd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial TensorProduct

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

section DvdBasis

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

private def tensorPolyAlgEquiv (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    (MvPolynomial (Fin n) R ⊗[R] A) ≃ₐ[R] MvPolynomial (Fin n) A :=
  (Algebra.TensorProduct.comm R (MvPolynomial (Fin n) R) A).trans
    ((algebraTensorAlgEquiv R A).restrictScalars R)

private theorem tensorPolyAlgEquiv_tmul (p : MvPolynomial (Fin n) R) (a : A) :
    tensorPolyAlgEquiv R A n (p ⊗ₜ a) = a • MvPolynomial.map (algebraMap R A) p := by
  simp [tensorPolyAlgEquiv]

private def tensorPolyEquiv (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    (MvPolynomial (Fin n) R ⊗[R] A) ≃ₗ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) A where
  toFun := tensorPolyAlgEquiv R A n
  invFun := (tensorPolyAlgEquiv R A n).symm
  map_add' := map_add _
  left_inv := (tensorPolyAlgEquiv R A n).symm_apply_apply
  right_inv := (tensorPolyAlgEquiv R A n).apply_symm_apply
  map_smul' q t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul p a =>
      rw [smul_tmul', smul_eq_mul, tensorPolyAlgEquiv_tmul, tensorPolyAlgEquiv_tmul, RingHom.id_apply,
        Algebra.smul_def q, MvPolynomial.algebraMap_def, map_mul, mul_smul_comm]
    | add s t hs ht =>
      rw [smul_add, map_add (f := _), map_add (f := _), hs, ht, smul_add]

private def tensorPolyBasis {ι : Type*} (b : Module.Basis ι R A) (n : ℕ) :
    Module.Basis ι (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) :=
  (Algebra.TensorProduct.basis (MvPolynomial (Fin n) R) b).map (tensorPolyEquiv R A n)

end DvdBasis

theorem NormFormDvd.proof : NormFormDvd.Statement := by
  intro R A _ _ _ _ _ n x p hdvd
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨h, hh⟩ := hdvd
  let b := Module.Free.chooseBasis R A
  let bP := tensorPolyBasis b n
  have hmap : (p.map (algebraMap R A) : MvPolynomial (Fin n) A) =
      algebraMap (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) p := by
    rw [MvPolynomial.algebraMap_def]
  have hnorm : Algebra.norm (MvPolynomial (Fin n) R)
      (algebraMap (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) p) = p ^ Module.finrank R A := by
    rw [Algebra.norm_algebraMap_of_basis bP, Module.finrank_eq_card_basis b]
  refine ⟨Algebra.norm (MvPolynomial (Fin n) R) h, ?_⟩
  rw [← hnorm, ← hmap, hh, map_mul]
  rfl

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParFracIsFractionRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem ParFracIsFractionRing.proof : ParFracIsFractionRing.Statement := by
  intro K _ _ e n v
  let := (parToFrac e n v).toAlgebra
  have : IsScalarTower (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (ParFrac K e n) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change _ = parToFrac e n v (algebraMap _ _ x)
      unfold parToFrac
      rw [IsLocalization.lift_eq]
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (parPrime e n v).primeCompl
    (ParDVR e n v) (ParFrac K e n)

end

end GroundTheory.Heights₂.Heights.Vertical
end

