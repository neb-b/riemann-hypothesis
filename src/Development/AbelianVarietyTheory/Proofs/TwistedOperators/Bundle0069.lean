module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitNormFormAtOddPlace
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlmostNormFinDiag
section
open NumberField IsDedekindDomain

namespace GlobalTheory.QuadSymbol

theorem AlmostNorm.exists_basis_sq (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] :
    ∃ (δ : K) (b : Module.Basis (Fin 2) K L), ¬ IsSquare δ ∧ b 0 = 1 ∧
      b 1 * b 1 = algebraMap K L δ := by
  have hr : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ hr
  have hc : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans hr
  haveI : Nontrivial (L ≃ₐ[K] L) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨σ, hσ⟩ := exists_ne (1 : L ≃ₐ[K] L)
  have h2 : σ * σ = 1 := by rw [← sq, ← hc]; exact pow_card_eq_one'
  obtain ⟨δ, b, h1, h0, -, h3⟩ := GlobalTheory.QuadNormBase.exists_basis K L (σ : L →ₐ[K] L) hr
    (fun x => by
      have := congrArg (fun τ : L ≃ₐ[K] L => τ x) h2
      simpa using this)
    (by
      by_contra h
      push Not at h
      exact hσ (AlgEquiv.ext h))
  exact ⟨δ, b, h1, h0, h3⟩

theorem almostNorm_finDiag :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [Algebra.IsQuadraticExtension K L], ∀ t : Kˣ, AlmostNorm K L (finDiag K t) := by
  intro K L _ _ _ _ _ _ t
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  refine (((GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 2 two_ne_zero)).union
    (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 δ hδ0))).union
    (GlobalTheory.QNorm.finite_valuation_ne_one K t)).subset ?_
  intro v hv
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, Units.val_mk0] at hn
  obtain ⟨⟨h2, hd⟩, ht⟩ := hn
  have key : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  obtain ⟨x, -, y, -, h⟩ := GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit K v
    (algebraMap K _ δ) (algebraMap K _ (t : K))
    (by rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2]; exact (key _).trans h2) (by rw [key, hd]) (by rw [key, ht])
  exact hv ((mem_normGroup_iff_form b h0 h1).2 ⟨x, y, h⟩)

end GlobalTheory.QuadSymbol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndIntegral
section
set_option autoImplicit false

noncomputable section

open IsDedekindDomain IsLocalRing Formalism.L2.Pj

namespace GlobalTheory.CompleteValExt

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem exists_algebraMap_eq_iff (x : K) : (∃ a : V, algebraMap V K a = x) ↔ 0 ≤ vV V x := by
  by_cases hx : x = 0
  · subst hx
    exact ⟨fun _ => by simp [vV], fun _ => ⟨0, map_zero _⟩⟩
  have h1 := WithZero.log_le_log (valV_ne_zero (V := V) hx) one_ne_zero
  rw [WithZero.log_one] at h1
  have h2 : 0 ≤ vV V x ↔ valV V x ≤ 1 := by
    rw [← h1]
    unfold vV
    omega
  rw [h2]
  refine ⟨?_, fun h => IsDiscreteValuationRing.exists_lift_of_le_one (A := V) (K := K) h⟩
  rintro ⟨a, rfl⟩
  exact HeightOneSpectrum.valuation_le_one _ a

variable {W L : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L]
  [IsFractionRing W L]

theorem finite_and_integral_of_scale [IsAdicComplete (maximalIdeal V) V] (i : K →+* L) {r : ℕ} (hr : 0 < r)
    (hi : ∀ z, vV W (i z) = (r : ℤ) * vV V z) (h' : Finite (ResidueField W)) :
    i.Finite ∧ ∀ b : W, (i.comp (algebraMap V K)).IsIntegralElem (algebraMap W L b) := by
  have hint : ∀ a : V, ∃ v : W, algebraMap W L v = i (algebraMap V K a) := fun a =>
    (exists_algebraMap_eq_iff _).2 (by
      rw [hi]; exact mul_nonneg (by positivity) ((exists_algebraMap_eq_iff _).1 ⟨a, rfl⟩))
  choose g0 hg0 using hint
  have hinj := IsFractionRing.injective W L
  let g : V →+* W :=
    { toFun := g0
      map_one' := hinj (by simp [hg0])
      map_mul' := fun a b => hinj (by simp [hg0])
      map_zero' := hinj (by simp [hg0])
      map_add' := fun a b => hinj (by simp [hg0]) }
  have hg : ∀ a, algebraMap W L (g a) = i (algebraMap V K a) := hg0
  letI : Algebra V W := g.toAlgebra
  letI : Algebra K L := i.toAlgebra
  letI : Algebra V L := (i.comp (algebraMap V K)).toAlgebra
  have : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun a => (hg a).symm
  have : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hgi : Function.Injective (algebraMap V W) := fun a b hab => by
    apply IsFractionRing.injective V K
    apply i.injective
    rw [← hg, ← hg]
    exact congrArg _ hab
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hgi
  have hle : (maximalIdeal V).map (algebraMap V W) ≤ maximalIdeal W := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal]
    intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb' : i (algebraMap V K a) * algebraMap W L b = 1 := by
      rw [← hg, ← map_mul, ← map_one (algebraMap W L)]
      exact congrArg _ hb
    have h0 : algebraMap V K a ≠ 0 := fun h => by
      rw [h, map_zero, zero_mul] at hb'
      exact zero_ne_one hb'
    have h1 : algebraMap W L b = i (algebraMap V K a)⁻¹ := by
      rw [map_inv₀]
      exact eq_inv_of_mul_eq_one_right hb'
    have h2 := (exists_algebraMap_eq_iff (V := W) _).1 ⟨b, h1⟩
    rw [hi] at h2
    obtain ⟨c, hc⟩ := (exists_algebraMap_eq_iff (V := V) _).2
      (nonneg_of_mul_nonneg_right h2 (by exact_mod_cast hr))
    refine (mem_maximalIdeal a).1 ha (IsUnit.of_mul_eq_one c (IsFractionRing.injective V K ?_))
    rw [map_mul, hc, map_one, mul_inv_cancel₀ h0]
  have hne : (maximalIdeal V).map (algebraMap V W) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hgi]
    exact IsDiscreteValuationRing.not_a_field V
  have htop : (maximalIdeal V).map (algebraMap V W) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal W).ne_top hle
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have : Finite (W ⧸ maximalIdeal W) := h'
  have : Module.Finite V W := GlobalTheory.finite_of_forall_prime_mem hϖ.ne_zero (fun P hP h0 => by
    rw [eq_maximalIdeal (hP.isMaximal h0)]
    exact hϖ.not_isUnit) hne htop
  refine ⟨Module.Finite.of_isLocalization V W (nonZeroDivisors V), fun b => ?_⟩
  exact (Algebra.IsIntegral.isIntegral (R := V) b).algebraMap (B := L)

theorem finite_and_integral : ∀ (T T' : CDVR) (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r →
    (∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) → T'.FinRes →
    i.Finite ∧ ∀ b : T'.V, (i.comp (algebraMap T.V T.Fr)).IsIntegralElem (algebraMap T'.V T'.Fr b) :=
  fun T T' i _ hr hi h' => finite_and_integral_of_scale (V := T.V) (W := T'.V) i hr hi h'

end GlobalTheory.CompleteValExt
end
end

