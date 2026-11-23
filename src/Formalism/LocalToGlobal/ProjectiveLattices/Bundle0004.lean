module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open MvPolynomial

variable (R : Type) [CommRing R] (ι : Type) (m : ℕ)

def orig : Ideal (MvPolynomial ι R) := Ideal.span (Set.range X)

abbrev Jet : Type := MvPolynomial ι R ⧸ orig R ι ^ (m + 1)

variable {R ι m}

theorem map_orig_pow {B : Type} [CommRing B] (f : MvPolynomial ι R →+* B) (k : ℕ) :
    Ideal.map f (orig R ι ^ k) = Ideal.span (Set.range fun i => f (X i)) ^ k := by
  rw [orig, Ideal.map_pow, Ideal.map_span, ← Set.range_comp]
  rfl

def liftJet {B : Type} [CommRing B] [Algebra R B] (f : MvPolynomial ι R →ₐ[R] B)
    (h : Ideal.span (Set.range fun i => f (X i)) ^ (m + 1) = ⊥) : Jet R ι m →ₐ[R] B :=
  Ideal.Quotient.liftₐ _ f fun a ha => by
    have : f a ∈ Ideal.map (f : MvPolynomial ι R →+* B) (orig R ι ^ (m + 1)) :=
      Ideal.mem_map_of_mem _ ha
    have h' : Ideal.span (Set.range fun i => (f : MvPolynomial ι R →+* B) (X i)) ^ (m + 1) = ⊥ := h
    rw [map_orig_pow, h'] at this
    exact (Submodule.mem_bot _).1 this

def jetMap {ι' : Type} (φ : ι → MvPolynomial ι' R) (hφ : ∀ i, φ i ∈ orig R ι') :
    Jet R ι m →ₐ[R] Jet R ι' m :=
  liftJet ((Ideal.Quotient.mkₐ R (orig R ι' ^ (m + 1))).comp (aeval φ)) (by
    apply le_bot_iff.1
    have h1 : Ideal.span (Set.range fun i =>
        ((Ideal.Quotient.mkₐ R (orig R ι' ^ (m + 1))).comp (aeval φ)) (X i)) =
        Ideal.map (Ideal.Quotient.mk (orig R ι' ^ (m + 1))) (Ideal.span (Set.range φ)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      congr 1
      ext x
      simp
    rw [h1, ← Ideal.map_pow]
    have h2 : Ideal.span (Set.range φ) ^ (m + 1) ≤ orig R ι' ^ (m + 1) :=
      Ideal.pow_right_mono (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hφ i)) _
    refine (Ideal.map_mono h2).trans ?_
    rw [Ideal.map_quotient_self])

theorem X_mem_orig {ι' : Type} (i : ι') : (X i : MvPolynomial ι' R) ∈ orig R ι' :=
  Ideal.subset_span ⟨i, rfl⟩

def jetIn {K : Type} (k : K) : Jet R ι m →ₐ[R] Jet R (K × ι) m :=
  jetMap (fun i => X (k, i)) fun i => X_mem_orig (k, i)

def jetScale (c : ι → R) : Jet R ι m →ₐ[R] Jet R ι m :=
  jetMap (fun i => C (c i) * X i) fun i => Ideal.mul_mem_left _ _ (X_mem_orig i)

def jetAug : Jet R ι m →ₐ[R] R :=
  liftJet (aeval fun _ => (0 : R)) (by
    have : Ideal.span (Set.range fun i => (aeval fun _ => (0 : R)) (X i : MvPolynomial ι R)) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      simp
    rw [this, Ideal.bot_pow (Nat.succ_ne_zero m)])

def jetTan [DecidableEq ι] (ℓ : ι) : Jet R ι (m + 1) →ₐ[R] DualNumber R :=
  liftJet (aeval fun i => if i = ℓ then (DualNumber.eps : DualNumber R) else 0) (by
    apply le_bot_iff.1
    have h1 : Ideal.span (Set.range fun i =>
        (aeval fun i => if i = ℓ then (DualNumber.eps : DualNumber R) else 0) (X i : MvPolynomial ι R))
        ≤ Ideal.span {(DualNumber.eps : DualNumber R)} := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases h : i = ℓ
      · simp [h]
      · simp [h]
    refine (Ideal.pow_right_mono h1 _).trans ?_
    refine (Ideal.pow_le_pow_right (show 2 ≤ m + 1 + 1 by omega)).trans ?_
    rw [Ideal.span_singleton_pow]
    simp)

theorem sub_const_mem_orig (P : MvPolynomial ι R) :
    P - C (MvPolynomial.constantCoeff P) ∈ orig R ι := by
  induction P using MvPolynomial.induction_on
  next a =>
    simp
  next p q hp hq =>
    have h : p + q - C (MvPolynomial.constantCoeff (p + q)) =
        (p - C (MvPolynomial.constantCoeff p)) + (q - C (MvPolynomial.constantCoeff q)) := by
      simp only [map_add (f := _)]
      ring
    rw [h]
    exact Ideal.add_mem _ hp hq
  next p n _ =>
    simp only [map_mul, constantCoeff_X, mul_zero, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ (X_mem_orig n)

def degLE [Fintype ι] [DecidableEq ι] (m : ℕ) : Finset (ι →₀ ℕ) :=
  ((Finset.univ : Finset (ι → Fin (m + 1))).image fun v =>
    Finsupp.equivFunOnFinite.symm fun i => (v i : ℕ)).filter fun e => (e.sum fun _ k => k) ≤ m

def psTrunc [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι R) : MvPolynomial ι R :=
  ∑ e ∈ degLE m, monomial e (MvPowerSeries.coeff e f)

def psJet [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι R) : Jet R ι m :=
  Ideal.Quotient.mk _ (psTrunc m f)

def jetSubstPS {ι' : Type} [Fintype ι'] [DecidableEq ι'] (φ : ι → MvPowerSeries ι' R) : Jet R ι m →ₐ[R] Jet R ι' m :=
  jetMap (fun i => psTrunc m (φ i) - C (MvPolynomial.constantCoeff (psTrunc m (φ i))))
    fun i => sub_const_mem_orig _

def jetTrunc : Jet R ι (m + 1) →ₐ[R] Jet R ι m :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
section
open NumberField Polynomial

namespace Formalism.L2.Pj

attribute [local instance] FractionRing.liftAlgebra

theorem unramBridge_holds : ∀ (K : Type) [Field K] [NumberField K] [IsCMField K],
    (∀ P : Ideal (𝓞 K), P.IsMaximal → ∃ θ : 𝓞 K,
      θ - RingOfIntegers.mapRingEquiv (IsCMField.complexConj K : K ≃+* K) θ ∉ P) →
    Algebra.Unramified (𝓞 (maximalRealSubfield K)) (𝓞 K) := by
  intro K _ _ _ hθ
  set F := maximalRealSubfield K with hF
  have hsep : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 K)) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv (𝓞 F) F).symm.toRingEquiv
          (FractionRing.algEquiv (𝓞 K) K).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (𝓞 F) F).symm
      (FractionRing.algEquiv (𝓞 K) K).symm _
  rw [Algebra.unramified_iff_forall]
  rintro ⟨Q, hQ⟩
  change Algebra.IsUnramifiedAt (𝓞 F) Q
  rcases eq_or_ne Q ⊥ with rfl | hne
  · exact Algebra.isUnramifiedAt_bot
  have hmax : Q.IsMaximal := hQ.isMaximal hne
  obtain ⟨θ, hθP⟩ := hθ Q hmax
  set θ' := RingOfIntegers.mapRingEquiv (IsCMField.complexConj K : K ≃+* K) θ with hθ'
  have hσ : θ' = IsCMField.ringOfIntegersComplexConj K θ := RingOfIntegers.ext rfl
  have hne' : θ - θ' ≠ 0 := fun h => hθP (h ▸ Ideal.zero_mem _)

  have hnotF : (θ : K) ∉ F := by
    intro hm
    apply hne'
    rw [sub_eq_zero, hσ]
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj]
    exact ((IsCMField.complexConj_eq_self_iff K _).mpr hm).symm

  have hfin : Module.finrank F K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F K
  have hint : IsIntegral F (θ : K) := Algebra.IsIntegral.isIntegral _
  have hadj : Algebra.adjoin F {algebraMap (𝓞 K) K θ} = ⊤ := by
    have : IsSimpleOrder (IntermediateField F K) :=
      IntermediateField.isSimpleOrder_of_finrank_prime F K (hfin ▸ Nat.prime_two)
    rcases eq_bot_or_eq_top (IntermediateField.adjoin F {(θ : K)}) with h | h
    · exfalso
      rw [IntermediateField.adjoin_simple_eq_bot_iff, IntermediateField.mem_bot] at h
      obtain ⟨y, hy⟩ := h
      exact hnotF (hy ▸ y.2)
    · rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
      change (IntermediateField.adjoin F {(θ : K)}).toSubalgebra = ⊤
      rw [h, IntermediateField.top_toSubalgebra]
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 F) F K θ hadj

  set f := minpoly (𝓞 F) θ with hf
  have hθint : IsIntegral (𝓞 F) θ := Algebra.IsIntegral.isIntegral _
  have hmonic : f.Monic := minpoly.monic hθint
  have hdeg : f.natDegree ≤ 2 := by
    have h1 : f = minpoly (𝓞 F) (algebraMap (𝓞 K) K θ) :=
      (minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 K) K) θ).symm
    have h2 := minpoly.isIntegrallyClosed_eq_field_fractions' F
      (IsIntegral.algebraMap hθint : IsIntegral (𝓞 F) (algebraMap (𝓞 K) K θ))
    have h3 : (minpoly F (algebraMap (𝓞 K) K θ)).natDegree ≤ 2 :=
      hfin ▸ minpoly.natDegree_le _
    rw [h2, Polynomial.natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective _ _)] at h3
    rw [h1]; exact h3
  set fK := f.map (algebraMap (𝓞 F) (𝓞 K)) with hfK
  have hKmonic : fK.Monic := hmonic.map _
  have hKdeg : fK.natDegree ≤ 2 := by
    rw [hfK, hmonic.natDegree_map]; exact hdeg
  have hr1 : fK.IsRoot θ := by
    rw [IsRoot, hfK, eval_map, ← aeval_def]; exact minpoly.aeval _ _
  have hr2 : fK.IsRoot θ' := by
    rw [IsRoot, hfK, eval_map, ← aeval_def, hσ]
    rw [show IsCMField.ringOfIntegersComplexConj K θ = (IsCMField.ringOfIntegersComplexConj K).toAlgHom θ from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  set g := fK /ₘ (X - C θ) with hg
  have hfg : (X - C θ) * g = fK := (mul_divByMonic_eq_iff_isRoot).mpr hr1
  have hg2 : g.IsRoot θ' := by
    have := hr2
    rw [← hfg, IsRoot, eval_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · exfalso; apply hne'; simp at h; rw [sub_eq_zero] at h ⊢; exact h.symm
    · exact h
  set h := g /ₘ (X - C θ') with hh
  have hgh : (X - C θ') * h = g := (mul_divByMonic_eq_iff_isRoot).mpr hg2
  have hfac : fK = (X - C θ) * ((X - C θ') * h) := by rw [hgh, hfg]
  have hhmonic : h.Monic := by
    have hm2 : ((X - C θ) * (X - C θ')).Monic := (monic_X_sub_C θ).mul (monic_X_sub_C θ')
    rw [hfac, ← mul_assoc] at hKmonic
    exact hm2.of_mul_monic_left hKmonic
  have hh1 : h = 1 := by
    rw [← hhmonic.natDegree_eq_zero]
    have := hKdeg
    rw [hfac, natDegree_mul (X_sub_C_ne_zero θ) (mul_ne_zero (X_sub_C_ne_zero θ') hhmonic.ne_zero),
      natDegree_mul (X_sub_C_ne_zero θ') hhmonic.ne_zero, natDegree_X_sub_C, natDegree_X_sub_C] at this
    omega
  have hval : aeval θ (derivative f) = θ - θ' := by
    rw [aeval_def, ← eval_map, ← derivative_map, ← hfK, hfac, hh1]
    simp [derivative_mul]
  rw [← not_dvd_differentIdeal_iff, Ideal.dvd_iff_le]
  intro hle
  exact hθP (hle (hval ▸ hmem))

end Formalism.L2.Pj
end

