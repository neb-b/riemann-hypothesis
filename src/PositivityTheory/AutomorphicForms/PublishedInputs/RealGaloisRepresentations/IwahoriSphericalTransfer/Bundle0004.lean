module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.SqrtFixedOfIsSquarePadic
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SqFix

theorem exists_int_sq_approx (q : ℕ) [Fact q.Prime] (d : ℤ) (h : IsSquare (d : ℚ_[q])) (n : ℕ) :
    ∃ x : ℤ, ((q : ℤ) ^ n) ∣ d - x ^ 2 := by
  obtain ⟨y, hy⟩ := h
  have hy1 : ‖y‖ ≤ 1 := by
    have h1 : ‖y‖ * ‖y‖ ≤ 1 := by
      rw [← norm_mul, ← hy]; exact Padic.norm_int_le_one d
    nlinarith [norm_nonneg y]
  set y' : ℤ_[q] := ⟨y, hy1⟩ with hy'
  set x : ℤ := ((PadicInt.toZModPow n y').val : ℤ) with hx
  refine ⟨x, ?_⟩
  have hmem : y' - (x : ℤ_[q]) ∈ (Ideal.span {(q : ℤ_[q]) ^ n} : Ideal ℤ_[q]) := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hx]
    simp
  have hd : ((d : ℤ) : ℤ_[q]) = y' * y' := by
    apply Subtype.ext
    simp [hy', hy]
    rfl
  have hmem2 : (((d - x ^ 2 : ℤ)) : ℤ_[q]) ∈ (Ideal.span {(q : ℤ_[q]) ^ n} : Ideal ℤ_[q]) := by
    have : (((d - x ^ 2 : ℤ)) : ℤ_[q]) = (y' - (x : ℤ_[q])) * (y' + (x : ℤ_[q])) := by
      push_cast; rw [hd]; ring
    rw [this]; exact Ideal.mul_mem_right _ _ hmem
  have := (PadicInt.norm_le_pow_iff_mem_span_pow _ n).mpr hmem2
  exact_mod_cast (PadicInt.norm_int_le_pow_iff_dvd (p := q)).mp this

end GlobalTheory.SqFix

namespace GlobalTheory.SqFix

theorem valuation_apply_le {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (s : G F Ω) (hs : s ∈ Dec (F := F) A) (z w : Ω)
    (h : A.valuation z ≤ A.valuation w) : A.valuation (s z) ≤ A.valuation (s w) := by
  by_cases hw : w = 0
  · subst hw
    have hz : z = 0 := by
      have : A.valuation z = 0 := le_antisymm (by simpa using h) zero_le'
      simpa using this
    subst hz; simp
  · have hsw : s w ≠ 0 := (map_ne_zero_iff _ s.injective).mpr hw
    have h1 : A.valuation (z / w) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ h zero_le'
    have h2 : s (z / w) ∈ A := (ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hs _).mpr ((A.valuation_le_one_iff _).mp h1)
    rw [map_div₀] at h2
    have h3 := (A.valuation_le_one_iff _).mpr h2
    rw [map_div₀] at h3
    have hv : A.valuation (s w) ≠ 0 := by simpa using hsw
    exact (div_le_one₀ (zero_lt_iff.mpr hv)).mp h3

end GlobalTheory.SqFix

namespace GlobalTheory.SqFix

theorem sqrt_fixed_of_isSquare_padic : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (q : ℕ) [Fact q.Prime], ((q : ℕ) : 𝓞 F) ∈ v.asIdeal → ∀ (d : ℤ) (δ : Ω), δ ^ 2 = (d : Ω) → IsSquare (d : ℚ_[q]) → ∀ s ∈ Dec (F := F) A, s δ = δ := by
  intro F Ω _ _ _ _ _ v A hA q _ hq d δ hδ hsq s hs
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hsδ2 : s δ ^ 2 = δ ^ 2 := by rw [← map_pow, hδ, map_intCast]
  by_cases hd : d = 0
  · subst hd
    have : δ = 0 := by simpa using hδ
    subst this; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsδ2 with h | h
  · exact h
  exfalso
  have hqv : A.valuation (q : Ω) < 1 := by
    have := (hA (q : 𝓞 F)).mpr hq
    simpa using this
  have hq0 : (q : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hN0 : (4 * d).natAbs ≠ 0 := by simp [hd]
  obtain ⟨k, u, hu, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 q (Fact.out : q.Prime).one_lt.ne'
  have hV4d : A.valuation (((4 * d : ℤ)) : Ω) = A.valuation (q : Ω) ^ k * A.valuation (u : Ω) := by
    rcases Int.natAbs_eq (4 * d) with e | e
    · rw [e, hN]; push_cast; rw [map_mul, map_pow]
    · rw [e, hN]; push_cast; rw [Valuation.map_neg, map_mul, map_pow]
  have hu1 : 1 ≤ A.valuation (u : Ω) := by
    refine not_lt.mp fun hlt => ?_
    have hu' : ((u : ℕ) : 𝓞 F) ∈ v.asIdeal := (hA (u : 𝓞 F)).mp (by simpa using hlt)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hu)
    have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
      have e := congrArg (Int.cast : ℤ → 𝓞 F) hab
      push_cast at e
      rw [← e]
      exact add_mem (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hu')
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨x, m, hm⟩ := exists_int_sq_approx q d hsq (k + 1)
  set a : Ω := δ - x with ha
  set b : Ω := δ + x with hb
  have hab : a * b = (q : Ω) ^ (k + 1) * (m : Ω) := by
    have e := congrArg (Int.cast : ℤ → Ω) hm
    push_cast at e
    rw [ha, hb, ← e, ← hδ]; ring
  have hsa : s a = -b := by rw [ha, hb, map_sub, map_intCast, h]; ring
  have hsb : s b = -a := by rw [ha, hb, map_add (f := _), map_intCast, h]; ring
  have hVab : A.valuation a = A.valuation b := by
    rcases le_total (A.valuation a) (A.valuation b) with e | e
    · refine le_antisymm e ?_
      have := valuation_apply_le A s hs a b e
      rwa [hsa, hsb, Valuation.map_neg, Valuation.map_neg] at this
    · refine le_antisymm ?_ e
      have := valuation_apply_le A s hs b a e
      rwa [hsa, hsb, Valuation.map_neg, Valuation.map_neg] at this
  have hm1 : A.valuation (m : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  have hVa : A.valuation a * A.valuation a ≤ A.valuation (q : Ω) ^ (k + 1) := by
    calc A.valuation a * A.valuation a = A.valuation (a * b) := by rw [map_mul, hVab]
      _ = A.valuation (q : Ω) ^ (k + 1) * A.valuation (m : Ω) := by rw [hab, map_mul, map_pow]
      _ ≤ A.valuation (q : Ω) ^ (k + 1) * 1 := mul_le_mul' le_rfl hm1
      _ = _ := mul_one _
  have h2δ : A.valuation (2 * δ) ≤ A.valuation a := by
    have e : 2 * δ = a + b := by rw [ha, hb]; ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans ?_
    rw [hVab, max_self]
  have h4d : A.valuation (((4 * d : ℤ)) : Ω) ≤ A.valuation (q : Ω) ^ (k + 1) := by
    have e : (((4 * d : ℤ)) : Ω) = (2 * δ) * (2 * δ) := by push_cast; rw [← hδ]; ring
    rw [e, map_mul]
    exact (mul_le_mul' h2δ h2δ).trans hVa
  have hqk : A.valuation (q : Ω) ^ k ≠ 0 := pow_ne_zero _ (by simpa using hq0)
  have key : A.valuation (q : Ω) ^ k * 1 ≤ A.valuation (q : Ω) ^ k * A.valuation (q : Ω) := by
    calc A.valuation (q : Ω) ^ k * 1 ≤ A.valuation (q : Ω) ^ k * A.valuation (u : Ω) := mul_le_mul' le_rfl hu1
      _ = A.valuation (((4 * d : ℤ)) : Ω) := hV4d.symm
      _ ≤ A.valuation (q : Ω) ^ (k + 1) := h4d
      _ = _ := pow_succ _ _
  have h3 := mul_le_mul' (le_refl (A.valuation (q : Ω) ^ k)⁻¹) key
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hqk, one_mul, one_mul] at h3
  have := h3
  exact absurd hqv (not_lt.mpr this)

end GlobalTheory.SqFix
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.SqrtNegMovedByInertia
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SqrtNegRam

open Polynomial

theorem valuation_natCast_eq {F : Type} [Field F] [NumberField F] {p : ℕ} (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ discr F) (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    v.valuation F (p : F) = WithZero.exp (-1 : ℤ) := by
  have h2 := GlobalTheory.LamTie.ExpCond.not_mem_sq_of_not_dvd_discr hp hd v hv
  have e : (p : F) = algebraMap (𝓞 F) F (p : 𝓞 F) := by simp
  rw [e, v.valuation_of_algebraMap]
  have h0 : ((p : ℕ) : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hne := v.intValuation_ne_zero _ h0
  have h1 := (v.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hv)
  have h2' := mt (v.intValuation_le_pow_iff_mem _ 2).1 h2
  rw [← WithZero.exp_log hne] at h1 h2' ⊢
  rw [WithZero.exp_le_exp] at h1 h2'
  rw [WithZero.exp_inj]
  push_cast at h1 h2'
  omega

theorem valuation_mul_ne_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr F) {δ : Ω}
    (hδ : δ ^ 2 = -(p : Ω)) {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) (hA : IsPlaceOver A v) (y : F) (hy : y ≠ 0) :
    A.valuation (algebraMap F Ω y * δ) ≠ 1 := by
  intro h
  obtain ⟨ι, hι⟩ := GlobalTheory.LocDict.exists_isLocEmb F Ω A v hA
  have hmem : ∀ e : F, algebraMap F Ω e ∈ A ↔ v.valuation F e ≤ 1 := fun e => by
    rw [hι, ι.commutes]; exact GlobalTheory.LocEmbExist.isIntegral_algebraMap_iff v e
  have he : algebraMap F Ω (y ^ 2 * p) = -(algebraMap F Ω y * δ) ^ 2 := by
    rw [mul_pow, hδ, map_mul, map_pow, map_natCast]; ring
  have hw : A.valuation (algebraMap F Ω (y ^ 2 * p)) = 1 := by
    rw [he, Valuation.map_neg, map_pow, h, one_pow]
  have h1 : v.valuation F (y ^ 2 * p) ≤ 1 := (hmem _).1 ((A.valuation_le_one_iff _).1 hw.le)
  have h2 : v.valuation F (y ^ 2 * p)⁻¹ ≤ 1 :=
    (hmem _).1 ((A.valuation_le_one_iff _).1 (by rw [map_inv₀, map_inv₀, hw, inv_one]))
  have hy0 : v.valuation F y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [map_inv₀] at h2
  rw [map_mul, map_pow, valuation_natCast_eq hp hd v hv, ← WithZero.exp_log hy0,
    ← WithZero.exp_nsmul, ← WithZero.exp_add] at h1 h2
  rw [← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  rw [nsmul_eq_mul] at h1 h2
  push_cast at h1 h2
  omega

end GlobalTheory.SqrtNegRam

namespace GlobalTheory.SqrtNegRam

open Polynomial

theorem sqrt_neg_moved_by_inertia : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (p : ℕ), p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ discr F → ∀ (δ : Ω), δ ^ 2 = -(p : Ω) → ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∃ s ∈ Ine (F := F) A, s δ ≠ δ := by
  intro F Ω _ _ _ _ _ p hp _ hd δ hδ v A hv hA
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have KL := valuation_mul_ne_one hp hd hδ hv hA
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    apply hp0
    linear_combination hδ
  set f : F[X] := X ^ 2 + C (p : F) with hfdef
  have hf_root : ∀ x : Ω, aeval x f = 0 ↔ x ^ 2 = -(p : Ω) := by
    intro x
    simp only [hfdef, map_add (f := _), map_pow, aeval_X, aeval_C, map_natCast]
    constructor <;> intro h <;> linear_combination h
  have hmon : f.Monic := monic_X_pow_add_C _ two_ne_zero
  have hirr : Irreducible f := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · rw [hfdef, natDegree_X_pow_add_C]; decide
    · intro c hc
      have hc' : (algebraMap F Ω c) ^ 2 = -(p : Ω) := by
        rw [← hf_root, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hc, map_zero]
      have hc0 : c ≠ 0 := by
        rintro rfl
        apply hp0
        rw [map_zero] at hc'
        linear_combination hc'
      have hc1 : (algebraMap F Ω c)⁻¹ * algebraMap F Ω c = 1 :=
        inv_mul_cancel₀ ((_root_.map_ne_zero _).2 hc0)
      have hfac : (algebraMap F Ω c - δ) * (algebraMap F Ω c + δ) = 0 := by
        linear_combination hc' - hδ
      rcases mul_eq_zero.1 hfac with h | h
      · apply KL c⁻¹ (inv_ne_zero hc0)
        rw [map_inv₀, ← sub_eq_zero.1 h, hc1, map_one]
      · apply KL c⁻¹ (inv_ne_zero hc0)
        have e : δ = -(algebraMap F Ω c) := by linear_combination h
        rw [e, mul_neg, map_inv₀, hc1, Valuation.map_neg, map_one]
  have hmin : f = minpoly F δ := minpoly.eq_of_irreducible_of_monic hirr ((hf_root δ).2 hδ) hmon
  have hmin' : f = minpoly F (-δ) :=
    minpoly.eq_of_irreducible_of_monic hirr ((hf_root _).2 (by rw [neg_sq]; exact hδ)) hmon
  obtain ⟨σ₀, hσ₀⟩ := (Normal.minpoly_eq_iff_mem_orbit Ω).1 (hmin'.symm.trans hmin)
  have hσ₀' : σ₀ δ = -δ := hσ₀
  let M : IntermediateField F Ω := IntermediateField.adjoin F (f.rootSet Ω)
  haveI : Polynomial.IsSplittingField F M f :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI : Normal F M := Normal.of_isSplittingField f
  haveI : FiniteDimensional F M := Polynomial.IsSplittingField.finiteDimensional M f
  haveI : IsGalois F M := ⟨⟩
  let τ : M ≃ₐ[F] M := σ₀.restrictNormal M
  have hδM : δ ∈ M := IntermediateField.subset_adjoin _ _
    (by rw [Polynomial.mem_rootSet]; exact ⟨hmon.ne_zero, (hf_root δ).2 hδ⟩)
  have hform : ∀ z ∈ M, ∃ a b : F, z = algebraMap F Ω a + algebraMap F Ω b * δ := by
    intro z hz
    have hz' : z ∈ Algebra.adjoin F (f.rootSet Ω) := by
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
        (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)]
      exact hz
    clear hz
    induction hz' using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Polynomial.mem_rootSet, hf_root] at hx
      have hfx : (x - δ) * (x + δ) = 0 := by linear_combination hx.2 - hδ
      rcases mul_eq_zero.1 hfx with h | h
      · exact ⟨0, 1, by rw [map_zero, map_one]; linear_combination h⟩
      · exact ⟨0, -1, by rw [map_zero, map_neg, map_one]; linear_combination h⟩
    | algebraMap r => exact ⟨r, 0, by rw [map_zero]; ring⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨c, d, rfl⟩ := hy
      exact ⟨a + c, b + d, by rw [map_add (f := _), map_add (f := _)]; ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨c, d, rfl⟩ := hy
      refine ⟨a * c - b * d * p, a * d + b * c, ?_⟩
      simp only [map_add (f := _), map_sub, map_mul, map_natCast]
      linear_combination (algebraMap F Ω b * algebraMap F Ω d) * hδ
  have hcond : ∀ x : M, A.valuation (algebraMap M Ω x) ≤ 1 →
      A.valuation (algebraMap M Ω (τ x) - algebraMap M Ω x) < 1 := by
    intro x hx
    rw [AlgEquiv.restrictNormal_commutes]
    obtain ⟨a, b, hab⟩ := hform (algebraMap M Ω x) x.2
    rw [hab] at hx ⊢
    have e : σ₀ (algebraMap F Ω a + algebraMap F Ω b * δ) - (algebraMap F Ω a + algebraMap F Ω b * δ)
        = (-2 : Ω) * (algebraMap F Ω b * δ) := by
      rw [map_add (f := _), map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hσ₀']; ring
    rw [e]
    have hb1 : A.valuation (algebraMap F Ω b * δ) < 1 := by
      by_cases hb : b = 0
      · rw [hb, map_zero, zero_mul, Valuation.map_zero]; exact zero_lt_one
      have hne1 := KL b hb
      have hne : A.valuation (algebraMap F Ω a) ≠ A.valuation (algebraMap F Ω b * δ) := by
        intro heq
        have hbd : algebraMap F Ω b * δ ≠ 0 := mul_ne_zero ((_root_.map_ne_zero _).2 hb) hδ0
        have ha : a ≠ 0 := by
          rintro rfl
          rw [map_zero, Valuation.map_zero] at heq
          exact hbd ((Valuation.zero_iff _).1 heq.symm)
        apply KL (b / a) (div_ne_zero hb ha)
        have haw : A.valuation (algebraMap F Ω a) ≠ 0 :=
          (Valuation.ne_zero_iff _).2 ((_root_.map_ne_zero _).2 ha)
        rw [map_div₀, div_mul_eq_mul_div, map_div₀, ← heq, div_self haw]
      rw [Valuation.map_add_of_distinct_val _ hne] at hx
      exact lt_of_le_of_ne (le_trans (le_max_right _ _) hx) hne1
    rw [map_mul]
    have h2 : A.valuation (-2 : Ω) ≤ 1 := by
      rw [Valuation.map_neg]
      have := valuation_natCast_le_one A 2
      simpa using this
    calc A.valuation (-2 : Ω) * A.valuation (algebraMap F Ω b * δ)
        ≤ 1 * A.valuation (algebraMap F Ω b * δ) := by gcongr
      _ < 1 := by rw [one_mul]; exact hb1
  obtain ⟨σ, hσ, hστ⟩ := GlobalTheory.InertiaLift.exists_mem_Ine_lift A M τ hcond
  refine ⟨σ, hσ, ?_⟩
  have h1 := hστ ⟨δ, hδM⟩
  rw [AlgEquiv.restrictNormal_commutes] at h1
  change σ δ = σ₀ δ at h1
  rw [h1, hσ₀']
  intro h
  have h2 : (2 : Ω) * δ = 0 := by linear_combination -h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact two_ne_zero h3
  · exact hδ0 h3

end GlobalTheory.SqrtNegRam
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.WdRelOfFrobSS
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WdResGen

private theorem wdAt_of_model {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
    {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces B) {a : ℕ}
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (L₂ : FinExt l) (r₂ : ↥(Dec (F := E) A) →* GL (Fin a) ↥L₂.1)
    (hm₂ : IsModel B r L₂ r₂) (hV₂ : IsPst P (B.repE L₂ r₂)) :
    wdAt P ι B h hj r = wdPst P ι B h hj (B.repE L₂ r₂) := by
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι B h hj (r := r) ⟨L₂, r₂, hm₂, hV₂⟩
  have h₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have h₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have e : mapRep (IntermediateField.inclusion h₁).toRingHom r₁ =
      mapRep (IntermediateField.inclusion h₂).toRingHom r₂ := by
    ext g i j
    exact congrArg (fun f : ↥(Dec (F := E) A) →* GL (Fin a) (Om l) => (f g : Matrix (Fin a) (Fin a) (Om l)) i j)
      (hm₁.2.trans hm₂.2.symm)
  rw [e₁, BridgeParam.wdPst_enlarge P ι B h hj h₁ r₁ hV₁, BridgeParam.wdPst_enlarge P ι B h hj h₂ r₂ hV₂, e]

private theorem wdRel_of_frobSS {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'} (φ : Ω ≃+* Ω')
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Weil h → Module.End ℂ V} {ρ' : Weil h' → Module.End ℂ V} {N : Module.End ℂ V}
    {a : WDRep h V} {b : WDRep h' V} (ha : IsFrobSS ρ N a) (hb : IsFrobSS ρ' N b)
    (hρ : ∀ σ σ', WeilRel φ σ σ' → ρ σ = ρ' σ') : WDRel φ (WD.mk a) (WD.mk b) := by
  let e := (Module.finBasis ℂ V).equivFun
  refine ⟨_, a.transport e, b.transport e, WD.sound (a.iso_transport e).symm, WD.sound (b.iso_transport e).symm,
    ?_, fun σ σ' hσ => ?_⟩
  · show e.conjAlgEquiv ℂ a.N = e.conjAlgEquiv ℂ b.N
    rw [ha.1, hb.1]
  · show e.conjAlgEquiv ℂ (a.ρ σ) = e.conjAlgEquiv ℂ (b.ρ σ')
    have h1 := hρ σ σ' hσ
    have h2 := hb.2 σ'
    rw [← h1] at h2
    rw [(Module.End.isNilpotent_isSemisimple_unique (ha.2 σ).2 (a.semisimple σ) h2.2 (b.semisimple σ')
      ((ha.2 σ).1.symm.sub_left (Commute.refl _)) (h2.1.symm.sub_left (Commute.refl _))
      (by simp)).2]

end GlobalTheory.WdResGen


open GlobalTheory.WdResGen in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.RealGal.wdRelRes_gen : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (P : LocPrime l) (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O), Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (a : ℕ) (r : G F Ω →* GL (Fin a) (Qbar l)), IsPstAt P Bw (r.comp (Dec (F := F) A).subtype) → ∀ (ι : Qbar l ≃+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i → WDRel (RingEquiv.refl Ω) (wdAt P ι Bw h hj (r.comp (Dec (F := F) A).subtype)) (wdAt P ι Bw' h' hj' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype)) := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ P A O _ _ _ Bw Bw' hK hJ hL n r hr ι v w h h' hj hj' i hP
  obtain ⟨Kw, j, j_E, j_dense, e, e_cont, e_symm_cont, e_comm, LL, LL_split, eO, eO_alg, eO_cont, eO_symm_cont⟩ := Bw'
  dsimp only at hK hJ hL
  subst hK hJ hL
  set Bw' : LocBridge l K Ω (Dec (F := K) A) O :=
    ⟨Bw.Kw, Bw.j, j_E, j_dense, e, e_cont, e_symm_cont, e_comm, Bw.LL, LL_split, eO, eO_alg, eO_cont, eO_symm_cont⟩
    with hB
  obtain ⟨L, r', hm, hV⟩ := hr
  have key : ∀ (g : ↥(Dec (F := K) A)) (x : Ω), ((Bw.e.symm (e g) : ↥(Dec (F := F) A)) : G F Ω) x = (g : G K Ω) x :=
    fun g x => Bw.j.injective (by rw [← Bw.e_comm, MulEquiv.apply_symm_apply, e_comm])
  let r'' : ↥(Dec (F := K) A) →* GL (Fin n) ↥L.1 := r'.comp (e.trans Bw.e.symm).toMonoidHom
  have hm' : IsModel Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype)
      L r'' := by
    refine ⟨hm.1, MonoidHom.ext fun g => ?_⟩
    have h1 := DFunLike.congr_fun hm.2 (Bw.e.symm (e g))
    refine h1.trans (congrArg r (AlgEquiv.ext (key g)))
  have hrep : Bw'.repE L r'' = Bw.repE L r' := by
    refine MonoidHom.ext fun g => ?_
    have h1 : r'' (e.symm g) = r' (Bw.e.symm g) := by simp [r'']
    exact congrArg (fun m : GL (Fin n) ↥L.1 => Matrix.toLin' (m : Matrix (Fin n) (Fin n) ↥L.1)) h1
  have hV' : IsPst P (Bw'.repE L r'') := by rw [hrep]; exact hV
  rw [wdAt_of_model _ ι Bw h hj _ L r' hm hV, wdAt_of_model _ ι Bw' h' hj' _ L r'' hm' hV', hrep]
  generalize Bw.repE L r' = ρ at hV ⊢
  haveI := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, wdPst_of_isPst ι Bw' h' hj' hV]
  obtain ⟨c, hc, hdeg, hq, -⟩ := _root_.GlobalTheory.WeilTransport.weil_equiv F Ω A v h K Ω A w h' _ _ i hP
  refine wdRel_of_frobSS _ (BridgeParam.isFrobSS_wdRep P ι Bw h hj ρ)
    (BridgeParam.isFrobSS_wdRep P ι Bw' h' hj' ρ) fun σ σ' hσ => ?_
  have h1 : weilToGK Bw h σ = weilToGK Bw' h' σ' := by
    have h2 : Subgroup.inclusion (Weil_le_Dec h) σ = Bw.e.symm (e (Subgroup.inclusion (Weil_le_Dec h') σ')) :=
      Subtype.ext (AlgEquiv.ext fun x => (hσ x).trans (key (Subgroup.inclusion (Weil_le_Dec h') σ') x).symm)
    exact (congrArg Bw.e h2).trans (Bw.e.apply_symm_apply _)
  have h3 : alpha l σ = alpha l σ' := by
    rw [alpha, alpha, ← (hc σ σ').1 hσ, hdeg, resDeg, resDeg, hq]
  have h4 : weilD Bw h P ρ σ = weilD Bw' h' P ρ σ' :=
    (weilD_apply Bw h P ρ σ).trans ((congrArg₂ (fun (g : ↥(GK Bw.Kw)) (m : ℤ) => actD P ρ g *
      Units.val (phiU P ρ ^ (-m)))
      h1 h3).trans (weilD_apply Bw' h' P ρ σ').symm)
  refine wd_ext _ ι ρ fun x => ?_
  exact (wdRho_mk P ι Bw h hj ρ σ x).trans
    ((congrArg (wdMk P ι ρ) (LinearMap.congr_fun h4 x)).trans (wdRho_mk P ι Bw' h' hj' ρ σ' x).symm)
end

