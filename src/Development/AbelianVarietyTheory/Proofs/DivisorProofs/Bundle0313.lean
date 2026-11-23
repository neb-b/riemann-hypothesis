module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePlaceOrdEqOne
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

open Polynomial

variable {k L : Type} [Field k] [Field L] [Algebra k L]

theorem place_aeval_le_one (x : L) (u : Place k L) (hx : u.1 x ≤ 1) (p : k[X]) :
    u.1 (aeval x p) ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [Algebra.smul_def, map_mul, map_pow]
  refine mul_le_one' ?_ (pow_le_one' hx _)
  by_cases hc : p.coeff i = 0
  · simp [hc]
  · rw [u.2.2 _ hc]

theorem place_aeval_eq_one (x : L) (u : Place k L) (hx : u.1 x < 1) (q : k[X]) (hq : q.coeff 0 ≠ 0) :
    u.1 (aeval x q) = 1 := by
  have h1 : u.1 (algebraMap k L (q.coeff 0)) = 1 := u.2.2 _ hq
  have h2 : u.1 (x * aeval x q.divX) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le hx (place_aeval_le_one x u hx.le _)
  conv_lhs => rw [← X_mul_divX_add q]
  rw [map_add (f := _), map_mul, aeval_X, aeval_C, Valuation.map_add_eq_of_lt_right u.1 (by rw [h1]; exact h2), h1]

theorem place_aeval_eq_pow (x : L) (u : Place k L) (hx : u.1 x < 1) (p : k[X]) (hp : p ≠ 0) :
    u.1 (aeval x p) = u.1 x ^ p.rootMultiplicity 0 := by
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 0
  have hq0 : q.coeff 0 ≠ 0 := by
    intro h; apply hq; simpa [X_dvd_iff] using h
  conv_lhs => rw [hpq]
  simp [map_mul, map_pow, place_aeval_eq_one x u hx q hq0]

end GlobalTheory.Nef

namespace GlobalTheory.Nef

open Polynomial

theorem exists_unique_place_ord_eq_one (k L : Type) [Field k] [Field L] [Algebra k L] (x : L)
    (hx : Transcendental k x) (htop : k⟮x⟯ = ⊤) :
    ∃ v : Place k L, ord v x = 1 ∧ ∀ w : Place k L, w.1 x < 1 → w = v := by
  have hmem : ∀ y : L, ∃ r s : k[X], y = aeval x r / aeval x s := fun y =>
    (IntermediateField.mem_adjoin_simple_iff (F := k) (α := x) y).1 (by rw [htop]; trivial)
  have hne : ∀ p : k[X], p ≠ 0 → aeval x p ≠ 0 := fun p hp h => hx ⟨p, hp, h⟩
  have hval : ∀ u : Place k L, u.1 x < 1 → u.1 x = WithZero.exp (-1 : ℤ) := by
    intro u hu
    have hx0 : u.1 x ≠ 0 := by
      rw [Valuation.ne_zero_iff]; intro h; apply hne X X_ne_zero; simpa using h
    set b := WithZero.log (u.1 x) with hb
    have hub : u.1 x = WithZero.exp b := (WithZero.exp_log hx0).symm
    have hb0 : b < 0 := by
      have : WithZero.exp b < WithZero.exp (0 : ℤ) := by rw [← hub, WithZero.exp_zero]; exact hu
      exact WithZero.exp_lt_exp.1 this
    obtain ⟨y, hy⟩ := u.2.1 (WithZero.exp (-1 : ℤ))
    obtain ⟨r, s, rfl⟩ := hmem y
    have hr : r ≠ 0 := by rintro rfl; simp at hy; exact WithZero.exp_ne_zero hy.symm
    have hs : s ≠ 0 := by rintro rfl; simp at hy; exact WithZero.exp_ne_zero hy.symm
    rw [map_div₀, place_aeval_eq_pow x u hu r hr, place_aeval_eq_pow x u hu s hs, hub,
      ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_sub, WithZero.exp_inj] at hy
    have hmul : b * ((r.rootMultiplicity 0 : ℤ) - s.rootMultiplicity 0) = -1 := by
      rw [← hy]; simp only [nsmul_eq_mul]; ring
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one hmul with h | h
    · omega
    · rw [hub, h]
  have hpol : ∀ u : Place k L, u.1 x < 1 → ∀ p : k[X], p ≠ 0 →
      u.1 (aeval x p) = WithZero.exp (-1 : ℤ) ^ p.rootMultiplicity 0 := fun u hu p hp => by
    rw [place_aeval_eq_pow x u hu p hp, hval u hu]
  let e : RatFunc k ≃ₐ[k] L := ((RatFunc.algEquivOfTranscendental x hx).trans
    (IntermediateField.equivOfEq htop)).trans IntermediateField.topEquiv
  have heX : e RatFunc.X = x := by simp [e]
  have heXs : e.symm x = RatFunc.X := by rw [← heX, AlgEquiv.symm_apply_apply]
  let V := (Polynomial.idealX k).valuation (RatFunc k)
  let v0 : Valuation L (WithZero (Multiplicative ℤ)) := V.comap (e.symm : L →+* RatFunc k)
  have hv0 : ∀ y, v0 y = V (e.symm y) := fun y => rfl
  have hVX : V RatFunc.X = WithZero.exp (-1 : ℤ) := by
    rw [← RatFunc.algebraMap_X, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ X_ne_zero (Polynomial.idealX_span k)
  let v : Place k L := ⟨v0, fun γ => by
      obtain ⟨r, hr⟩ := RatFunc.valuation_surjective (K := k) γ
      exact ⟨e r, by rw [hv0, AlgEquiv.symm_apply_apply]; exact hr⟩,
    fun c hc => by
      rw [hv0, AlgEquiv.commutes, IsScalarTower.algebraMap_apply k k[X] (RatFunc k),
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
      intro hmem'
      rw [Polynomial.idealX_span, Ideal.mem_span_singleton, X_dvd_iff] at hmem'
      simp [hc] at hmem'⟩
  have hvx : v.1 x = WithZero.exp (-1 : ℤ) := by
    show v0 x = _; rw [hv0, heXs, hVX]
  refine ⟨v, by simp [ord, hvx], fun w hw => ?_⟩
  have hvl : v.1 x < 1 := by rw [hvx]; exact WithZero.exp_lt_exp.2 (by norm_num) |>.trans_eq WithZero.exp_zero
  apply Subtype.ext
  ext y
  obtain ⟨r, s, rfl⟩ := hmem y
  rw [map_div₀, map_div₀]
  by_cases hr : r = 0
  · simp [hr]
  by_cases hs : s = 0
  · simp [hs]
  rw [hpol w hw r hr, hpol w hw s hs, hpol v hvl r hr, hpol v hvl s hs]

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryMulIntegralOfNormMaximalOrderUnit
section
noncomputable section

open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.UnitAdj

theorem isIntegral_or_isIntegral_inv {O K L : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L] [Algebra O L]
    [IsScalarTower O K L] [FiniteDimensional K L] (y : L) :
    IsIntegral O y ∨ IsIntegral O y⁻¹ := by
  haveI := GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure O K L
  haveI := integralClosure.isFractionRing_of_finite_extension (A := O) K L
  rcases ValuationRing.isInteger_or_isInteger (integralClosure O L) y with ⟨z, hz⟩ | ⟨z, hz⟩
  · left; rw [← hz]; exact z.2
  · right; rw [← hz]; exact z.2

theorem isIntegral_of_mul_self_eq {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {e : A}
    (he : e * e = e) : IsIntegral O e := by
  refine ⟨X ^ 2 - X, monic_X_pow_sub (degree_X_le.trans_lt (by norm_num)), ?_⟩
  simp [eval₂_sub, pow_two, he]

section Residues

variable {A : Type} [CommRing A] [IsArtinianRing A] [IsReduced A]

theorem eq_zero_of_forall_mem {y : A} (h : ∀ I : MaximalSpectrum A, y ∈ I.asIdeal) : y = 0 := by
  apply (IsArtinianRing.equivPi A).injective
  rw [map_zero]
  funext I
  rw [IsArtinianRing.equivPi_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (h I)

theorem isIntegral_of_residues {O : Type} [CommRing O] [Algebra O A] {y : A}
    (h : ∀ I : MaximalSpectrum A, IsIntegral O (Ideal.Quotient.mk I.asIdeal y)) :
    IsIntegral O y := by
  let ψ : A ≃ₐ[O] (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    (IsArtinianRing.equivPi A).restrictScalars O
  refine (isIntegral_algHom_iff ψ.toAlgHom ψ.injective).1 ?_
  refine GlobalTheory.UnitLemma.PrincipalLat.isIntegral_pi' _ fun I => ?_
  have : ψ.toAlgHom y I = Ideal.Quotient.mk I.asIdeal y := IsArtinianRing.equivPi_apply A y I
  rw [this]
  exact h I

theorem exists_residues_indicator (P : MaximalSpectrum A → Prop) :
    ∃ e : A, ∀ I : MaximalSpectrum A, (P I → e - 1 ∈ I.asIdeal) ∧ (¬ P I → e ∈ I.asIdeal) := by
  classical
  let v : ∀ I : MaximalSpectrum A, A ⧸ I.asIdeal := fun I => if P I then 1 else 0
  refine ⟨(IsArtinianRing.equivPi A).symm v, fun I => ⟨fun hP => ?_, fun hP => ?_⟩⟩
  · have h1 := congrFun ((IsArtinianRing.equivPi A).apply_symm_apply v) I
    rw [IsArtinianRing.equivPi_apply] at h1
    rw [← Ideal.Quotient.eq, h1, map_one]
    simp [v, hP]
  · have h1 := congrFun ((IsArtinianRing.equivPi A).apply_symm_apply v) I
    rw [IsArtinianRing.equivPi_apply] at h1
    rw [← Ideal.Quotient.eq_zero_iff_mem, h1]
    simp [v, hP]

end Residues

theorem exists_unitary_mul_integral : ∀ {O K A : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Algebra K A] [Algebra O A] [IsScalarTower O K A] [Module.Finite K A] [IsReduced A]
    (σ : K →+* K), (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    ∀ τ : A →+* A, (∀ a, τ (τ a) = a) → (∀ k, τ (algebraMap K A k) = algebraMap K A (σ k)) →
    ∀ x : Aˣ, IsIntegral O (τ (x : A) * x) → IsIntegral O (τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A)) →
    ∃ t : Aˣ, τ (t : A) * t = 1 ∧ IsIntegral O ((t : A) * ((x⁻¹ : Aˣ) : A)) ∧
      IsIntegral O (((t⁻¹ : Aˣ) : A) * (x : A)) := by
  intro O K A _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ τ hτ hτσ x hc hci
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A

  have hinj := IsFractionRing.injective O K
  choose s hs using hσ
  let σO : O →+* O :=
    { toFun := s
      map_one' := hinj (by simp [← hs])
      map_mul' := fun a b => hinj (by simp [← hs])
      map_zero' := hinj (by simp [← hs])
      map_add' := fun a b => hinj (by simp [← hs]) }
  have hτO : ∀ a : O, τ (algebraMap O A a) = algebraMap O A (σO a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply O K A, hτσ]
    change _ = algebraMap O A (s a)
    rw [hs, ← IsScalarTower.algebraMap_apply]

  have hsurj : Function.Surjective τ := fun a => ⟨τ a, hτ a⟩
  obtain ⟨tI, hmem, htt⟩ : ∃ tI : MaximalSpectrum A → MaximalSpectrum A,
      (∀ I y, y ∈ (tI I).asIdeal ↔ τ y ∈ I.asIdeal) ∧ ∀ I, tI (tI I) = I := by
    have hmax : ∀ I : MaximalSpectrum A, (I.asIdeal.comap τ).IsMaximal := fun I => by
      haveI := I.isMaximal
      exact Ideal.comap_isMaximal_of_surjective τ hsurj
    refine ⟨fun I => ⟨I.asIdeal.comap τ, hmax I⟩, fun I y => Iff.rfl, fun I => ?_⟩
    ext y
    change τ (τ y) ∈ I.asIdeal ↔ y ∈ I.asIdeal
    rw [hτ]

  obtain ⟨e, he⟩ := exists_residues_indicator (fun I : MaximalSpectrum A => WellOrderingRel I (tI I))
  have he1 : ∀ I, WellOrderingRel I (tI I) → e - 1 ∈ I.asIdeal := fun I => (he I).1
  have he0 : ∀ I, ¬ WellOrderingRel I (tI I) → e ∈ I.asIdeal := fun I => (he I).2
  have hτe1 : ∀ I, WellOrderingRel (tI I) I → τ e - 1 ∈ I.asIdeal := by
    intro I h
    have := he1 (tI I) (by rw [htt]; exact h)
    rw [hmem, map_sub, map_one] at this
    exact this
  have hτe0 : ∀ I, ¬ WellOrderingRel (tI I) I → τ e ∈ I.asIdeal := by
    intro I h
    exact (hmem I e).1 (he0 (tI I) (by rw [htt]; exact h))
  have hee : e * e = e := by
    refine sub_eq_zero.1 (eq_zero_of_forall_mem fun I => ?_)
    by_cases hP : WellOrderingRel I (tI I)
    · have := I.asIdeal.mul_mem_left e (he1 I hP)
      rwa [mul_sub, mul_one] at this
    · exact I.asIdeal.sub_mem (I.asIdeal.mul_mem_left e (he0 I hP)) (he0 I hP)
  have hgg : τ e * τ e = τ e := by rw [← map_mul, hee]
  have heg : e * τ e = 0 := by
    refine eq_zero_of_forall_mem fun I => ?_
    by_cases hP : WellOrderingRel I (tI I)
    · exact I.asIdeal.mul_mem_left _ (hτe0 I (asymm_of WellOrderingRel hP))
    · exact I.asIdeal.mul_mem_right _ (he0 I hP)

  set f : A := 1 - e - τ e with hf
  have hfix : ∀ I, tI I = I → f - 1 ∈ I.asIdeal := by
    intro I hI
    have h0 : ¬ WellOrderingRel I (tI I) := by rw [hI]; exact irrefl_of WellOrderingRel I
    have h0' : ¬ WellOrderingRel (tI I) I := by rw [hI]; exact irrefl_of WellOrderingRel I
    have : f - 1 = -(e + τ e) := by rw [hf]; ring
    rw [this]
    exact I.asIdeal.neg_mem (I.asIdeal.add_mem (he0 I h0) (hτe0 I h0'))
  have hmov : ∀ I, tI I ≠ I → f ∈ I.asIdeal := by
    intro I hI
    rcases trichotomous_of WellOrderingRel I (tI I) with h | h | h
    · have : f = -(e - 1) - τ e := by rw [hf]; ring
      rw [this]
      exact I.asIdeal.sub_mem (I.asIdeal.neg_mem (he1 I h)) (hτe0 I (asymm_of WellOrderingRel h))
    · exact absurd h.symm hI
    · have : f = -(τ e - 1) - e := by rw [hf]; ring
      rw [this]
      exact I.asIdeal.sub_mem (I.asIdeal.neg_mem (hτe1 I h)) (he0 I (asymm_of WellOrderingRel h))

  set a : A := (x : A) with ha
  set b : A := ((x⁻¹ : Aˣ) : A) with hb
  have hab : a * b = 1 := x.mul_inv
  have hpq : τ a * τ b = 1 := by rw [← map_mul, hab, map_one]

  have hstable : ∀ I : MaximalSpectrum A, tI I = I →
      IsIntegral O (Ideal.Quotient.mk I.asIdeal a) ∧ IsIntegral O (Ideal.Quotient.mk I.asIdeal b) := by
    intro I hI
    have hle : I.asIdeal ≤ I.asIdeal.comap τ := fun y hy => by
      rw [Ideal.mem_comap, ← hmem, hI]; exact hy
    let ρ := Ideal.quotientMap I.asIdeal τ hle
    have hρ : ∀ y, ρ (Ideal.Quotient.mk I.asIdeal y) = Ideal.Quotient.mk I.asIdeal (τ y) :=
      fun y => Ideal.quotientMap_mk
    have hcomp : (algebraMap O (A ⧸ I.asIdeal)).comp σO = ρ.comp (algebraMap O (A ⧸ I.asIdeal)) := by
      ext r
      change Ideal.Quotient.mk _ (algebraMap O A (σO r)) = ρ (Ideal.Quotient.mk _ (algebraMap O A r))
      rw [hρ, hτO]
    have hρi : ∀ z, IsIntegral O z → IsIntegral O (ρ z) := fun z hz =>
      IsIntegral.map_of_comp_eq σO ρ hcomp hz
    have hmk : ∀ y : A, IsIntegral O y → IsIntegral O (Ideal.Quotient.mk I.asIdeal y) :=
      fun y hy => hy.map (Ideal.Quotient.mkₐ O I.asIdeal)
    have hxa : a = (τ a * a) * τ b := by linear_combination -a * hpq
    have hxb : b = (τ b * b) * τ a := by linear_combination -b * hpq
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional K (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    have hX : Ideal.Quotient.mk I.asIdeal a * Ideal.Quotient.mk I.asIdeal b = 1 := by
      rw [← map_mul, hab, map_one]
    have hinv : (Ideal.Quotient.mk I.asIdeal a)⁻¹ = Ideal.Quotient.mk I.asIdeal b :=
      inv_eq_of_mul_eq_one_right hX
    rcases isIntegral_or_isIntegral_inv (O := O) (K := K) (Ideal.Quotient.mk I.asIdeal a) with h | h
    · refine ⟨h, ?_⟩
      rw [hxb, map_mul, ← hρ]
      exact (hmk _ hci).mul (hρi _ h)
    · rw [hinv] at h
      refine ⟨?_, h⟩
      rw [hxa, map_mul, ← hρ]
      exact (hmk _ hc).mul (hρi _ h)
  have haf : IsIntegral O (a * f) ∧ IsIntegral O (b * f) := by
    constructor <;>
    · refine isIntegral_of_residues fun I => ?_
      by_cases hI : tI I = I
      · have h1 : Ideal.Quotient.mk I.asIdeal f = 1 := by
          rw [← map_one (Ideal.Quotient.mk I.asIdeal)]
          exact Ideal.Quotient.eq.2 (hfix I hI)
        rw [map_mul, h1, mul_one]
        first | exact (hstable I hI).1 | exact (hstable I hI).2
      · rw [Ideal.Quotient.eq_zero_iff_mem.2 (I.asIdeal.mul_mem_left _ (hmov I hI))]
        exact isIntegral_zero

  set T : A := a * e + τ b * τ e + f with hT
  set S : A := b * e + τ a * τ e + f with hS
  have hTS : T * S = 1 := by
    rw [hT, hS, hf]
    linear_combination e ^ 2 * hab + τ e ^ 2 * hpq + (2 - a - b) * hee + (2 - τ a - τ b) * hgg +
      (a * τ a + b * τ b - a - b - τ a - τ b + 2) * heg
  have hτT : τ T = S := by
    rw [hT, hS, hf]
    simp only [map_add (f := _), map_sub, map_mul, map_one, hτ]
    ring
  have ie : IsIntegral O e := isIntegral_of_mul_self_eq hee
  have ig : IsIntegral O (τ e) := isIntegral_of_mul_self_eq hgg
  refine ⟨Units.mkOfMulEqOne T S hTS, ?_, ?_, ?_⟩
  · change τ T * T = 1
    rw [hτT, mul_comm, hTS]
  · change IsIntegral O (T * b)
    have : T * b = e + (τ b * b) * τ e + b * f := by
      rw [hT]; linear_combination e * hab
    rw [this]
    exact (ie.add (hci.mul ig)).add haf.2
  · change IsIntegral O (S * a)
    have : S * a = e + (τ a * a) * τ e + a * f := by
      rw [hS]; linear_combination e * hab
    rw [this]
    exact (ie.add (hc.mul ig)).add haf.1

end GlobalTheory.UnitAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FTermIteratedFDerivBound
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.TermBound

theorem factorSmooth (σ : ℂ) (hσ : σ ∈ halfPlane) (ν β : ℝ) (hβ : β ≠ 0) :
    ContDiffOn ℝ ∞ (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ)) *
      hTrans σ ν (β * w.im)) {w : ℂ | 0 < w.im} := by
  have hre : ContDiff ℝ ∞ (fun w : ℂ => ((ν * β * w.re : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul Complex.reCLM.contDiff)
  have h1 : ContDiff ℝ ∞ (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ))) :=
    Complex.contDiff_exp.comp (contDiff_const.mul hre)
  have h2 : ContDiffOn ℝ ∞ (fun w : ℂ => hTrans σ ν (β * w.im)) {w : ℂ | 0 < w.im} := by
    refine (GlobalTheory.HeckeTwo.TermSmooth.contDiffOn_hTrans σ hσ ν).comp
      (contDiff_const.mul Complex.imCLM.contDiff : ContDiff ℝ ∞ fun w : ℂ => β * w.im).contDiffOn ?_
    intro w hw; exact mul_ne_zero hβ (ne_of_gt hw)
  exact h1.contDiffOn.mul h2

theorem fTerm_iteratedFDeriv_bound : ∀ (F : Type) [Field F] [NumberField F] (K : Set ℂ), IsCompact K → K ⊆ halfPlane →
    ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ, ∃ m : ℕ, ∀ N : ℕ, ∃ C : ℝ,
      ∀ σ ∈ K, ∀ z ∈ L, ∀ b ν : F, b ≠ 0 → ν ≠ 0 →
        ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z b ν) z‖ ≤
          C * ∏ τ : Emb F, (|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N := by
  intro F _ _ K hK hKH L hL hLH n
  obtain ⟨c, c', hc, hcc⟩ := _root_.GlobalTheory.isCompact_pi_upperHalfPlane_im_bounds (Emb F) L hL (fun z hz τ => hLH hz τ)
  have hfb := _root_.GlobalTheory.HeckeTwo.FactorBound.norm_iteratedFDeriv_fourierFactor_le (_root_.GlobalTheory.HeckeTwo.TermBoundDeriv.iteratedDeriv_hTrans_bound _root_.GlobalTheory.HeckeTwo.TermSmooth.iteratedDeriv_hTrans_repr _root_.GlobalTheory.HeckeTwo.TermDecay.intT_bound) K hK hKH c c' hc
  choose mk hmk using hfb
  refine ⟨(Finset.range (n + 1)).sup mk, fun N => ?_⟩
  choose Ck hCk using fun k => hmk k N
  refine ⟨n.factorial * (∑ k ∈ Finset.range (n + 1), max (Ck k) 0) ^ Fintype.card (Emb F), ?_⟩
  intro σ hσ z hz b ν hb hν
  have hσH : σ ∈ halfPlane := hKH hσ
  set m := (Finset.range (n + 1)).sup mk with hm
  set C0 := ∑ k ∈ Finset.range (n + 1), max (Ck k) 0 with hC0
  set g : Emb F → ℂ → ℂ := fun τ w => Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ b * w.re : ℝ) : ℂ)) *
    hTrans σ (τ ν) (τ b * w.im) with hg
  have hfun : (fun z : Emb F → ℂ => fTerm σ z b ν) = fun z => ∏ τ, g τ (z τ) := rfl
  have hτb : ∀ τ : Emb F, τ b ≠ 0 := fun τ => (map_ne_zero τ).2 hb
  have hτν : ∀ τ : Emb F, τ ν ≠ 0 := fun τ => (map_ne_zero τ).2 hν
  have hsm : ∀ τ, ContDiffOn ℝ ∞ (g τ) {w : ℂ | 0 < w.im} := fun τ => factorSmooth σ hσH (τ ν) (τ b) (hτb τ)
  have hopen : ∀ τ : Emb F, IsOpen {w : ℂ | 0 < w.im} := fun _ => isOpen_lt continuous_const Complex.continuous_im
  rw [hfun]
  refine (_root_.GlobalTheory.LeibnizProd.norm_iteratedFDeriv_prod_apply_le (Emb F) g (fun _ => {w : ℂ | 0 < w.im}) hopen hsm z (fun τ => hLH hz τ) n).trans ?_
  have hfac : ∀ τ, ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k (g τ) (z τ)‖ ≤
      C0 * ((|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N) := by
    intro τ
    rw [hC0, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    have h1 := hCk k σ hσ (τ ν) (τ b) (hτν τ) (hτb τ) (z τ) (hcc z hz τ).1 (hcc z hz τ).2
    have hB1 : (1 : ℝ) ≤ |τ b| + |τ b|⁻¹ := by
      have hp : 0 < |τ b| := abs_pos.2 (hτb τ)
      rcases le_total 1 |τ b| with h | h
      · linarith [inv_pos.2 hp]
      · have : 1 ≤ |τ b|⁻¹ := (one_le_inv₀ hp).2 h
        linarith
    have hmk' : mk k ≤ m := Finset.le_sup hk
    have hpow : (|τ b| + |τ b|⁻¹) ^ mk k ≤ (|τ b| + |τ b|⁻¹) ^ m := pow_le_pow_right₀ hB1 hmk'
    have hden : 0 < (1 + |τ ν * τ b|) ^ N := by positivity
    calc ‖iteratedFDeriv ℝ k (g τ) (z τ)‖ ≤ Ck k * (|τ b| + |τ b|⁻¹) ^ mk k / (1 + |τ ν * τ b|) ^ N := h1
      _ ≤ max (Ck k) 0 * ((|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N) := by
        rw [mul_div_assoc]
        exact mul_le_mul (le_max_left _ _) (div_le_div_of_nonneg_right hpow hden.le) (by positivity)
          (le_max_right _ _)
  calc (n.factorial : ℝ) * ∏ τ, ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k (g τ) (z τ)‖
      ≤ n.factorial * ∏ τ : Emb F, (C0 * ((|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N)) := by
        exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun τ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (fun τ _ => hfac τ)) (by positivity)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]; ring

end GlobalTheory.HeckeTwo.TermBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstMaximalMinorLocallyConstant
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem isFirstMax_eventually (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) :
    IsFirstMax Y J → ∀ᶠ Y' in nhds Y, IsFirstMax Y' J := by
  rintro ⟨h0, hle⟩
  have hm : valuation k (minor Y J) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have hc : ∀ J' : Fin a ↪ Fin d, Continuous fun Y' : Matrix (Fin a) (Fin d) k => minor Y' J' := fun J' =>
    (continuous_id.matrix_submatrix id J').matrix_det
  have key : ∀ J' : Fin a ↪ Fin d, ∀ᶠ Y' in nhds Y,
      valuation k (minor Y' J') = valuation k (minor Y J') ∨
        (minor Y J' = 0 ∧ valuation k (minor Y' J') < valuation k (minor Y J)) := by
    intro J'
    by_cases hz : minor Y J' = 0
    · have hn : {x : k | valuation k x < ((Units.mk0 _ hm : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)}
          ∈ nhds (0 : k) := (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 _ hm, subset_rfl⟩
      have hca := (hc J').continuousAt (x := Y)
      rw [ContinuousAt, hz] at hca
      filter_upwards [hca hn] with Y' hY'
      exact Or.inr ⟨hz, hY'⟩
    · have hne : valuation k (minor Y J') ≠ 0 := (Valuation.ne_zero_iff _).2 hz
      filter_upwards [(hc J').continuousAt (x := Y) ((valuation k).locally_const hne)] with Y' hY'
      exact Or.inl hY'
  have hall := Filter.eventually_all.2 key
  filter_upwards [hall] with Y' hY'
  have hJ : valuation k (minor Y' J) = valuation k (minor Y J) := by
    rcases hY' J with h | ⟨h, -⟩
    · exact h
    · exact absurd h h0
  refine ⟨(Valuation.ne_zero_iff _).1 (hJ ▸ hm), fun J' => ?_⟩
  rw [hJ]
  rcases hY' J' with h | ⟨-, h⟩
  · rw [h]; exact hle J'
  · exact ⟨h.le, fun _ => h⟩

end GlobalTheory.RankFibreKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLTrivialOrthogonalHyperplStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_trivial_orthogonal_hyperplaneFixer : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → 0 < b → ∀ (α : GL (Fin a) F → ℂ) (Y : GL (Fin n) F → ℂ), IsChar ℂ ℂ Y → HFree Y → ∑ᶠ x, hc a b α (fun _ => 1) n x * star (Y x) = 0 := by
  first | (exact @GlobalTheory.Shin.hc_one_orth_hfree) | (exact GlobalTheory.Shin.hc_one_orth_hfree) | (intros; apply GlobalTheory.Shin.hc_one_orth_hfree  <;> assumption)
end

