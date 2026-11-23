module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0176

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingOpenSubgroupsFinite
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.BoxCosetSum

variable {F : Type} [Field F] [NumberField F]

theorem continuous_evalV' (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) :=
  RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v

theorem eventually_evalV_mem_integers (x : FiniteAdeleRing (𝓞 F) F) :
    ∀ᶠ v in Filter.cofinite, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ v.adicCompletionIntegers F := x.2

theorem isOpen_box (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBo : ∀ v, IsOpen (B v : Set (v.adicCompletion F)))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) :
    IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ B v} := by
  have hT : {v | ¬ (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 hBf
  have hO : IsOpen {x : FiniteAdeleRing (𝓞 F) F |
      ∀ v, x v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  have e : {x : FiniteAdeleRing (𝓞 F) F | ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ B v} =
      {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} ∩
        ⋂ v ∈ hT.toFinset, (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) ⁻¹' (B v : Set (v.adicCompletion F)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      Set.Finite.mem_toFinset, SetLike.mem_coe]
    constructor
    · intro h
      exact ⟨fun v => hBO v (h v), fun v _ => h v⟩
    · rintro ⟨h1, h2⟩ v
      by_cases hv : (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F
      · have : x v ∈ (B v : Set (v.adicCompletion F)) := by rw [hv]; exact h1 v
        exact this
      · exact h2 v hv
  rw [e]
  exact hO.inter (isOpen_biInter_finset fun v _ => (hBo v).preimage (continuous_evalV' v))

def boxSub (κ : Type) (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)) :
    AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {u | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v}
  add_mem' := by
    intro a b ha hb i v
    simp only [Pi.add_apply, map_add (f := _)]
    exact (B v).add_mem (ha i v) (hb i v)
  zero_mem' := by
    intro i v
    simp only [Pi.zero_apply, map_zero]
    exact (B v).zero_mem
  neg_mem' := by
    intro a ha i v
    simp only [Pi.neg_apply, map_neg]
    exact (B v).neg_mem (ha i v)

theorem mem_boxSub {κ : Type} {B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)}
    {u : κ → FiniteAdeleRing (𝓞 F) F} :
    u ∈ boxSub κ B ↔ ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v := Iff.rfl

theorem isOpen_boxSub (κ : Type) [Finite κ] (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBo : ∀ v, IsOpen (B v : Set (v.adicCompletion F)))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) :
    IsOpen (boxSub κ B : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have e : (boxSub κ B : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      ⋂ i, (fun u : κ → FiniteAdeleRing (𝓞 F) F => u i) ⁻¹'
        {x : FiniteAdeleRing (𝓞 F) F | ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ B v} := by
    ext u
    simp only [SetLike.mem_coe, mem_boxSub, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
  rw [e]
  exact isOpen_iInter_of_finite fun i => (isOpen_box B hBo hBO hBf).preimage (continuous_apply i)

theorem finprod_indicator_eq (κ : Type) [Finite κ]
    (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F)
    (r y : κ → FiniteAdeleRing (𝓞 F) F) :
    (∏ᶠ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
          (1 : (κ → v.adicCompletion F) → ℂ) (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i))) =
      Set.indicator {z | z - r ∈ boxSub κ B} (fun _ => (1 : ℂ)) y := by
  have key : ∀ v, ((fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
      {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}) ↔
      ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈ B v := by
    intro v
    simp only [Set.mem_setOf_eq, Pi.sub_apply, map_sub]
  by_cases h : y - r ∈ boxSub κ B
  · rw [Set.indicator_of_mem (show y ∈ {z | z - r ∈ boxSub κ B} from h)]
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [Set.indicator_of_mem ((key v).2 fun i => h i v), Pi.one_apply]
  · rw [Set.indicator_of_notMem (show y ∉ {z | z - r ∈ boxSub κ B} from h)]
    rw [mem_boxSub] at h
    push_neg at h
    obtain ⟨i0, v0, hv0⟩ := h
    apply finprod_eq_zero _ v0
    · rw [Set.indicator_of_notMem]
      rw [key v0]
      exact fun H => hv0 (H i0)
    · have hT : {v | ¬ (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F}.Finite :=
        Filter.eventually_cofinite.1 hBf
      have hI : (⋃ i, {v | ¬ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈ v.adicCompletionIntegers F}).Finite :=
        Set.finite_iUnion fun i => Filter.eventually_cofinite.1 (eventually_evalV_mem_integers ((y - r) i))
      refine (hT.union hI).subset ?_
      intro v hv
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_not, not_exists] at hc
      apply hv
      dsimp only
      rw [Set.indicator_of_mem, Pi.one_apply]
      rw [key v]
      intro i
      have h2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈
          ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := hc.2 i
      rw [← hc.1] at h2
      exact h2

theorem eq_sum_finprod_box_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (B v : Set (v.adicCompletion F))) →
    (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) →
    (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ, HasCompactSupport g →
      (∀ y u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v) → g (y + u) = g y) →
      ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F), g = ∑ r ∈ R, g r • fun y : κ → FiniteAdeleRing (𝓞 F) F =>
        ∏ᶠ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
          (1 : (κ → v.adicCompletion F) → ℂ) (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  intro F _ _ κ _ B hBo hBO hBf g hg hinv
  classical
  set U := boxSub κ B with hU
  have hUo : IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) := isOpen_boxSub κ B hBo hBO hBf
  have hK : IsCompact (tsupport g) := hg
  have hcov : tsupport g ⊆ ⋃ y : (κ → FiniteAdeleRing (𝓞 F) F), {x | x - y ∈ U} := by
    intro x _
    exact Set.mem_iUnion.2 ⟨x, by simp [U.zero_mem]⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y => {x | x - y ∈ U})
    (fun y => hUo.preimage (continuous_id.sub continuous_const)) hcov
  let R : Finset (κ → FiniteAdeleRing (𝓞 F) F) :=
    (t.image (QuotientAddGroup.mk : (κ → FiniteAdeleRing (𝓞 F) F) → _ ⧸ U)).image Quotient.out
  have hdist : ∀ r ∈ R, ∀ r' ∈ R, ∀ x, x - r ∈ U → x - r' ∈ U → r = r' := by
    intro r hr r' hr' x h h'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hr'
    have e1 : (QuotientAddGroup.mk q.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    have e2 : (QuotientAddGroup.mk q'.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    rw [QuotientAddGroup.out_eq'] at e1 e2
    rw [e1, e2]
  have hcover : ∀ x ∈ tsupport g, ∃ r ∈ R, x - r ∈ U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine ⟨(QuotientAddGroup.mk y : _ ⧸ U).out, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hy), ?_⟩
    have e : -(QuotientAddGroup.mk y : _ ⧸ U).out + y ∈ U :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := U.add_mem hxy e
    convert this using 1
    abel
  refine ⟨R, ?_⟩
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, finprod_indicator_eq κ B hBO hBf]
  by_cases hx : ∃ r ∈ R, x - r ∈ U
  · obtain ⟨r0, hr0, hxr0⟩ := hx
    rw [Finset.sum_eq_single_of_mem r0 hr0]
    · rw [Set.indicator_of_mem (show x ∈ {z | z - r0 ∈ boxSub κ B} from hxr0), mul_one]
      have := hinv r0 (x - r0) hxr0
      rwa [add_sub_cancel] at this
    · intro r hr hne
      have hm : x ∉ {z | z - r ∈ boxSub κ B} := fun h => hne (hdist r hr r0 hr0 _ h hxr0)
      rw [Set.indicator_of_notMem hm, mul_zero]
  · push_neg at hx
    have hK' : x ∉ tsupport g := fun h => by
      obtain ⟨r, hr, h'⟩ := hcover _ h
      exact hx r hr h'
    rw [image_eq_zero_of_notMem_tsupport hK']
    symm
    apply Finset.sum_eq_zero
    intro r hr
    have hm : x ∉ {z | z - r ∈ boxSub κ B} := hx r hr
    rw [Set.indicator_of_notMem hm, mul_zero]

end GlobalTheory.BoxCosetSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepIntPolyRootModPrimeSq
section
open scoped TensorProduct Polynomial

namespace GlobalTheory

open Polynomial

theorem int_bezout_derivative_of_separable (f : ℤ[X])
    (hf : (f.map (Int.castRingHom ℚ)).Separable) :
    ∃ A B : ℤ[X], ∃ N : ℤ, N ≠ 0 ∧ A * f + B * derivative f = C N := by
  obtain ⟨a, b, hab⟩ := hf
  obtain ⟨c1, hc1_mem, hc1⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) a
  obtain ⟨c2, hc2_mem, hc2⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) b
  set A := IsLocalization.integerNormalization (nonZeroDivisors ℤ) a
  set B := IsLocalization.integerNormalization (nonZeroDivisors ℤ) b
  refine ⟨c2 • A, c1 • B, c1 * c2, ?_, ?_⟩
  · exact mul_ne_zero (nonZeroDivisors.ne_zero hc1_mem) (nonZeroDivisors.ne_zero hc2_mem)
  · apply Polynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
    have e1 : A.map (Int.castRingHom ℚ) = (c1 : ℚ) • a := by
      rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hc1]
      exact (Int.cast_smul_eq_zsmul ℚ _ _).symm
    have e2 : B.map (Int.castRingHom ℚ) = (c2 : ℚ) • b := by
      rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hc2]
      exact (Int.cast_smul_eq_zsmul ℚ _ _).symm
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_smul, Polynomial.map_C,
      ← Polynomial.derivative_map, e1, e2]
    rw [smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul]
    calc _ = C ((c1 : ℚ) * (c2 : ℚ)) *
            (a * map (Int.castRingHom ℚ) f + b * derivative (map (Int.castRingHom ℚ) f)) := by
          rw [C_mul]; simp only [eq_intCast]; ring
      _ = _ := by rw [hab, mul_one]; simp

theorem sep_int_poly_root_mod_prime_sq :
    ∀ f : ℤ[X], 0 < f.natDegree → (f.map (Int.castRingHom ℚ)).Separable →
      ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, ((p : ℤ) ^ 2) ∣ f.eval x := by
  intro f hdeg hsep n
  obtain ⟨A, B, N, hN, hAB⟩ := int_bezout_derivative_of_separable f hsep
  obtain ⟨p, hp, hnp, x, hx⟩ := _root_.GlobalTheory.exists_prime_gt_dvd_eval f hdeg (max n N.natAbs)
  refine ⟨p, hp, lt_of_le_of_lt (le_max_left _ _) hnp, ?_⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hev : A.eval x * f.eval x + B.eval x * (derivative f).eval x = N := by
    have := congrArg (Polynomial.eval x) hAB
    simpa using this
  have hpN : ¬ (p : ℤ) ∣ N := by
    intro h
    have h1 := Int.natAbs_dvd_natAbs.mpr h
    simp only [Int.natAbs_natCast] at h1
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hN) h1
    have h3 := lt_of_le_of_lt (le_max_right n N.natAbs) hnp
    omega
  have hpd : ¬ (p : ℤ) ∣ (derivative f).eval x := by
    intro h
    apply hpN
    rw [← hev]
    exact dvd_add (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_right h _)
  have hcop : IsCoprime ((derivative f).eval x) (p : ℤ) := by
    rw [isCoprime_comm]
    exact (Prime.coprime_iff_not_dvd hpZ).mpr hpd
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨k, hk⟩ := hx
  obtain ⟨K, hK⟩ := Polynomial.binomExpansion f x ((p : ℤ) * (-(k * u)))
  refine ⟨x + (p : ℤ) * (-(k * u)), ?_⟩
  rw [hK, hk]
  refine ⟨k * v + K * (k * u) ^ 2, ?_⟩
  have : k = k * (u * (derivative f).eval x + v * p) := by rw [huv, mul_one]
  linear_combination (p : ℤ) * this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelUnipotentAntidiagonalCorner
section
open GlobalTheory.WeilM
open scoped Matrix

namespace GlobalTheory.SiegelUnip
open Matrix

variable {R : Type} [CommRing R] {n : ℕ}

abbrev adR (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n) (Fin n ⊕ Fin n) R := fromCols 1 (-1)

abbrev adC (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n ⊕ Fin n) (Fin n) R := fromRows 1 (-1)

abbrev dgC (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n ⊕ Fin n) (Fin n) R := diagCols (Fin n)

theorem adR_mul_dgC : adR n R * dgC n R = 0 := by
  simp [diagCols, fromCols_mul_fromRows]

theorem adR_mul_adC : adR n R * adC n R = 2 • (1 : Matrix (Fin n) (Fin n) R) := by
  simp [fromCols_mul_fromRows, two_smul]

theorem dbl_mul_dgC (J₀ : Matrix (Fin n) (Fin n) R) : dbl J₀ * dgC n R = adC n R * J₀ := by
  rw [dbl, dgC, diagCols, fromBlocks_mul_fromRows, adC, fromRows_mul]
  simp

theorem dgC_tr_mul_dbl (J₀ : Matrix (Fin n) (Fin n) R) : (dgC n R)ᵀ * dbl J₀ = J₀ * adR n R := by
  rw [dbl, dgC, diagCols, transpose_fromRows, fromCols_mul_fromBlocks, adR, mul_fromCols]
  simp

theorem dgC_tr_dbl_dgC (J₀ : Matrix (Fin n) (Fin n) R) : (dgC n R)ᵀ * dbl J₀ * dgC n R = 0 := by
  rw [dgC_tr_mul_dbl, Matrix.mul_assoc, adR_mul_dgC, Matrix.mul_zero]

theorem adR_tr : (adR n R)ᵀ = adC n R := by
  simp [adR, adC, transpose_fromCols]

theorem dgC_map {R₀ : Type} [CommRing R₀] [Algebra R₀ R] (c : R →ₐ[R₀] R) : (dgC n R).map c = dgC n R := by
  rw [dgC, diagCols, fromRows_map, Matrix.map_one _ (map_zero c) (map_one c)]

theorem adR_map {R₀ : Type} [CommRing R₀] [Algebra R₀ R] (c : R →ₐ[R₀] R) : (adR n R).map c = adR n R := by
  rw [adR, fromCols_map, Matrix.map_neg _ (map_neg c), Matrix.map_one _ (map_zero c) (map_one c)]

end GlobalTheory.SiegelUnip


open Matrix GlobalTheory.SiegelUnip in
theorem GlobalTheory.siegel_unip_corner : ∀ {R₀ R : Type} [CommRing R₀] [CommRing R] [Algebra R₀ R] [Invertible (2 : R)] (c : R →ₐ[R₀] R) {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (x : Matrix (Fin n) (Fin n) R), xᵀ * J₀ + J₀ * x.map c = 0 → ∃ p : UG c (dbl J₀), (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) * diagCols (Fin n) = diagCols (Fin n) * (1 : Matrix (Fin n) (Fin n) R) ∧ ∀ h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R, Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * (h * p.1.1) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) = Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) + Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * diagCols (Fin n) * x := by
  intro R₀ R _ _ _ _ c n J₀ x hx
  set N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := GlobalTheory.SiegelUnip.dgC n R * x * GlobalTheory.SiegelUnip.adR n R with hN
  have hNN : N * N = 0 := by
    rw [hN, show GlobalTheory.SiegelUnip.dgC n R * x * GlobalTheory.SiegelUnip.adR n R * (GlobalTheory.SiegelUnip.dgC n R * x * GlobalTheory.SiegelUnip.adR n R) = GlobalTheory.SiegelUnip.dgC n R * x * (GlobalTheory.SiegelUnip.adR n R * GlobalTheory.SiegelUnip.dgC n R) * x * GlobalTheory.SiegelUnip.adR n R by
      simp only [Matrix.mul_assoc], GlobalTheory.SiegelUnip.adR_mul_dgC, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]
  have hsq : (⅟(2 : R) • N) * (⅟(2 : R) • N) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hNN, smul_zero, smul_zero]
  have hPQ : (1 + ⅟(2 : R) • N) * (1 - ⅟(2 : R) • N) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, hsq]; abel
  have hQP : (1 - ⅟(2 : R) • N) * (1 + ⅟(2 : R) • N) = 1 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hsq]; abel
  have hc2 : c (⅟(2 : R)) = ⅟(2 : R) := by
    refine (invOf_eq_right_inv ?_).symm
    have := congrArg c (mul_invOf_self (2 : R))
    rwa [map_mul, map_ofNat, map_one] at this
  have hNc : N.map c = GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R := by
    change (GlobalTheory.SiegelUnip.dgC n R * x * GlobalTheory.SiegelUnip.adR n R).map (c.toRingHom : R → R) = _
    rw [Matrix.map_mul, Matrix.map_mul]
    exact congrArg₂ _ (congrArg₂ _ (GlobalTheory.SiegelUnip.dgC_map c) rfl) (GlobalTheory.SiegelUnip.adR_map c)
  have hPc : (1 + ⅟(2 : R) • N).map c = 1 + ⅟(2 : R) • (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R) := by
    rw [Matrix.map_add _ (map_add c), Matrix.map_one _ (map_zero c) (map_one c), ← hNc]
    congr 1
    ext i j
    simp [hc2]
  have hNt : Nᵀ = GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ := by
    rw [hN, Matrix.transpose_mul, Matrix.transpose_mul, GlobalTheory.SiegelUnip.adR_tr, Matrix.mul_assoc]
  have hmem : (1 + ⅟(2 : R) • N)ᵀ * dbl J₀ * (1 + ⅟(2 : R) • N).map c = dbl J₀ := by
    rw [hPc, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, hNt]
    have e1 : dbl J₀ * (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R) = GlobalTheory.SiegelUnip.adC n R * (J₀ * x.map c) * GlobalTheory.SiegelUnip.adR n R := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SiegelUnip.dbl_mul_dgC]; simp only [Matrix.mul_assoc]
    have e2 : GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀ = GlobalTheory.SiegelUnip.adC n R * (xᵀ * J₀) * GlobalTheory.SiegelUnip.adR n R := by
      rw [Matrix.mul_assoc, GlobalTheory.SiegelUnip.dgC_tr_mul_dbl]; simp only [Matrix.mul_assoc]
    have e3 : GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀ * (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R) = 0 := by
      rw [show GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀ * (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R) =
        GlobalTheory.SiegelUnip.adC n R * xᵀ * ((GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀ * GlobalTheory.SiegelUnip.dgC n R) * x.map c * GlobalTheory.SiegelUnip.adR n R by simp only [Matrix.mul_assoc],
        GlobalTheory.SiegelUnip.dgC_tr_dbl_dgC]
      simp
    have e4 : GlobalTheory.SiegelUnip.adC n R * (J₀ * x.map c) * GlobalTheory.SiegelUnip.adR n R + GlobalTheory.SiegelUnip.adC n R * (xᵀ * J₀) * GlobalTheory.SiegelUnip.adR n R = 0 := by
      rw [← Matrix.add_mul, ← Matrix.mul_add, add_comm, hx, Matrix.mul_zero, Matrix.zero_mul]
    calc (1 + ⅟(2 : R) • (GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ)) * dbl J₀ * (1 + ⅟(2 : R) • (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R))
        = dbl J₀ + ⅟(2 : R) • (dbl J₀ * (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R)) +
          ⅟(2 : R) • (GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀) +
          (⅟(2 : R) * ⅟(2 : R)) • (GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀ * (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R)) := by
          simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; abel
      _ = dbl J₀ + ⅟(2 : R) • (GlobalTheory.SiegelUnip.adC n R * (J₀ * x.map c) * GlobalTheory.SiegelUnip.adR n R + GlobalTheory.SiegelUnip.adC n R * (xᵀ * J₀) * GlobalTheory.SiegelUnip.adR n R) := by
          rw [e3, e1, e2, smul_zero, add_zero, smul_add, add_assoc]
      _ = dbl J₀ := by rw [e4, smul_zero, add_zero]
  let u : GL (Fin n ⊕ Fin n) R := ⟨1 + ⅟(2 : R) • N, 1 - ⅟(2 : R) • N, hPQ, hQP⟩
  refine ⟨⟨u, hmem⟩, ?_, fun h => ?_⟩
  · have hp : ((⟨u, hmem⟩ : UG c (dbl J₀)) : GL (Fin n ⊕ Fin n) R).1 = 1 + ⅟(2 : R) • N := rfl
    rw [hp]
    have hpd : N * GlobalTheory.SiegelUnip.dgC n R = 0 := by rw [hN, Matrix.mul_assoc, GlobalTheory.SiegelUnip.adR_mul_dgC, Matrix.mul_zero]
    have key : ((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) + ⅟(2 : R) • N) * GlobalTheory.SiegelUnip.dgC n R =
        GlobalTheory.SiegelUnip.dgC n R * (1 : Matrix (Fin n) (Fin n) R) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hpd, smul_zero, add_zero, Matrix.mul_one]
    exact key
  · have hp : ((⟨u, hmem⟩ : UG c (dbl J₀)) : GL (Fin n ⊕ Fin n) R).1 = 1 + ⅟(2 : R) • N := rfl
    rw [hp]
    have e : GlobalTheory.SiegelUnip.adR n R * (h * N) * GlobalTheory.SiegelUnip.adC n R = (2 : R) • (GlobalTheory.SiegelUnip.adR n R * h * GlobalTheory.SiegelUnip.dgC n R * x) := by
      rw [hN, show GlobalTheory.SiegelUnip.adR n R * (h * (GlobalTheory.SiegelUnip.dgC n R * x * GlobalTheory.SiegelUnip.adR n R)) * GlobalTheory.SiegelUnip.adC n R = GlobalTheory.SiegelUnip.adR n R * h * GlobalTheory.SiegelUnip.dgC n R * x * (GlobalTheory.SiegelUnip.adR n R * GlobalTheory.SiegelUnip.adC n R) by
        simp only [Matrix.mul_assoc], GlobalTheory.SiegelUnip.adR_mul_adC, Matrix.mul_smul, Matrix.mul_one, two_smul, two_smul]
    rw [mul_add, mul_one, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, e, smul_smul,
      invOf_mul_self, one_smul, Matrix.mul_assoc (GlobalTheory.SiegelUnip.adR n R) h]
    rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionLiftNilpotentOfSqZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecLift

theorem lift_of_nilpotent_of_sqZero :
    (∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e) →
  ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e := by
  intro H
  suffices key : ∀ n : ℕ, ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π →
      RingHom.ker π ^ n = ⊥ →
      ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) →
      Smooth X.hom →
      ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e by
    intro R R₀ _ _ π hπ hnil
    obtain ⟨n, hn⟩ := hnil
    exact key n R R₀ π hπ hn
  intro n
  induction n with
  | zero =>
    intro R R₀ _ _ π hπ hn
    refine H R R₀ π hπ ?_
    exact le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.zero_le 2)).trans hn.le)
  | succ n ih =>
    intro R R₀ _ _ π hπ hn X X₀ i hi hX e₀ he₀
    by_cases hn2 : n + 1 ≤ 2
    · exact H R R₀ π hπ (le_bot_iff.mp ((Ideal.pow_le_pow_right hn2).trans hn.le)) X X₀ i hi hX e₀ he₀
    have hn1 : 1 ≤ n := by omega
    set I := RingHom.ker π with hIdef
    set J : Ideal R := I ^ n with hJdef
    have hJI : J ≤ RingHom.ker π := Ideal.pow_le_self (by omega)
    let q : R →+* R ⧸ J := Ideal.Quotient.mk J
    let π'' : R ⧸ J →+* R₀ := Ideal.Quotient.lift J π (fun a ha => (RingHom.mem_ker).mp (hJI ha))
    have hcomp : π''.comp q = π := by
      ext a; rfl
    have hsp : spMap π = spMap π'' ≫ spMap q := by
      rw [← hcomp]
      simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    have hπ'' : Function.Surjective π'' := Ideal.Quotient.lift_surjective_of_surjective J _ hπ
    have hkerq : RingHom.ker q = J := Ideal.mk_ker
    have hkerπ'' : RingHom.ker π'' = I.map q := by
      have := RingHom.comap_ker π'' q
      rw [hcomp] at this
      rw [← Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective (RingHom.ker π''), this]
    have hn'' : RingHom.ker π'' ^ n = ⊥ := by
      rw [hkerπ'', ← Ideal.map_pow]
      exact Ideal.map_quotient_self J
    have hJ2 : RingHom.ker q ^ 2 = ⊥ := by
      rw [hkerq, hJdef, ← pow_mul]
      exact le_bot_iff.mp ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
    let X' : Over (Sp (R ⧸ J)) := Over.mk (pullback.snd X.hom (spMap q))
    have hX' : Smooth X'.hom := show Smooth (pullback.snd X.hom (spMap q)) from inferInstance
    have hw : i ≫ X.hom = (X₀.hom ≫ spMap π'') ≫ spMap q := by
      rw [hi.w, hsp, Category.assoc]
    let i' : X₀.left ⟶ X'.left := pullback.lift i (X₀.hom ≫ spMap π'') hw
    have hi'1 : i' ≫ pullback.fst X.hom (spMap q) = i := pullback.lift_fst _ _ _
    have hi'2 : i' ≫ X'.hom = X₀.hom ≫ spMap π'' := pullback.lift_snd _ _ _
    have hi' : IsPullback i' X₀.hom X'.hom (spMap π'') := by
      refine IsPullback.of_right (h₁₂ := pullback.fst X.hom (spMap q)) (h₂₂ := spMap q) (v₁₃ := X.hom) ?_ hi'2
        (IsPullback.of_hasPullback X.hom (spMap q))
      rw [hi'1, ← hsp]
      exact hi
    obtain ⟨e', he'1, he'2⟩ := ih (R ⧸ J) R₀ π'' hπ'' hn'' X' X₀ i' hi' hX' e₀ he₀
    obtain ⟨e, he1, he2⟩ := H R (R ⧸ J) q Ideal.Quotient.mk_surjective hJ2 X X'
      (pullback.fst X.hom (spMap q)) (IsPullback.of_hasPullback X.hom (spMap q)) hX e' he'1
    refine ⟨e, he1, ?_⟩
    calc e₀ ≫ i = e₀ ≫ i' ≫ pullback.fst X.hom (spMap q) := by rw [hi'1]
      _ = (spMap π'' ≫ e') ≫ pullback.fst X.hom (spMap q) := by rw [← Category.assoc, he'2]
      _ = spMap π'' ≫ spMap q ≫ e := by rw [Category.assoc, he2]
      _ = spMap π ≫ e := by rw [hsp, Category.assoc]

end GlobalTheory.SecLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqMulFinrankMatrixAlgebraHomEqFinrankMulStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_mul_finrank_matrixAlgebra_hom_eq_finrank_mul : ∀ (k : Type) [Field k] (m : ℕ) (X Y : Type) [AddCommGroup X] [Module k X] [FiniteDimensional k X] [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y] (ρX : Matrix (Fin m) (Fin m) k →ₐ[k] Module.End k X) (ρY : Matrix (Fin m) (Fin m) k →ₐ[k] Module.End k Y), m ^ 2 * Module.finrank k (GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) = Module.finrank k X * Module.finrank k Y := by
  first | (exact @GlobalTheory.MatCount.count) | (exact GlobalTheory.MatCount.count) | (intros; apply GlobalTheory.MatCount.count <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryConjMapsKerAevalBasisAndGramStatement
section
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_conj_maps_ker_aeval_basis_and_gram : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K), ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * (g : Matrix (Fin n) (Fin n) K) = 1 → ∀ (Q : K[X]) {ι : Type} (u : ι → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q)) → LinearIndependent K (fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) ∧ Submodule.span K (Set.range fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) = LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)) ∧ (Matrix.of fun i j => ∑ k, σ (((g : Matrix (Fin n) (Fin n) K) *ᵥ u i) k) * ((g : Matrix (Fin n) (Fin n) K) *ᵥ u j) k) = Matrix.of fun i j => ∑ k, σ (u i k) * u j k := by
  first | exact @GlobalTheory.unitary_conj_ker_basis_gram | exact GlobalTheory.unitary_conj_ker_basis_gram | (intros; apply GlobalTheory.unitary_conj_ker_basis_gram <;> assumption)
end

