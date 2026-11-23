module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0004
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0163
public import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
public import ReciprocityTheory.ThetaQuasiPeriods.Transl
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0243
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparableNormalisationReducedFibres
section
open Polynomial

namespace GlobalTheory
open GroundTheory.FunctionField GroundTheory.Arith.SchemeCoh KaehlerDifferential

theorem ringKrullDim_eq_one_of_isDedekindDomain_of_not_isField (A : Type) [CommRing A] [IsDedekindDomain A] (h : ¬ IsField A) : ringKrullDim A = 1 := by
  have hle : ringKrullDim A ≤ 1 := Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 A)
  have h0 : ringKrullDim A ≠ 0 := fun h0 => h (by
      have : Ring.KrullDimLE 0 A := by
        rw [Ring.krullDimLE_iff, h0]
        rfl
      exact Ring.KrullDimLE.isField_of_isDomain)
  have hnn : 0 ≤ ringKrullDim A := ringKrullDim_nonneg_of_nontrivial
  generalize ringKrullDim A = d at hle h0 hnn ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd hnn (by simp)
  | coe n =>
    have h1 : n ≤ 1 := by exact_mod_cast hle
    have h2 : n ≠ 0 := by exact_mod_cast h0
    rw [le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h2)]
    rfl

theorem exists_aeval_finite_of_ringKrullDim_eq_one : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A],
    ringKrullDim A = 1 → ∃ t : A, (Polynomial.aeval (R := k) t).Finite := by
  intro k A _ _ _ _ _ hdim
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  have hs : ringKrullDim A = s := by
    let _ : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
    have _ : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨fun x => hfin.to_isIntegral x⟩
    have _ : FaithfulSMul (MvPolynomial (Fin s) k) A :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 hg
    rw [GlobalTheory.ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin s) k) A,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hs1 : s = 1 := by
    rw [hdim] at hs
    exact_mod_cast hs.symm
  subst hs1
  refine ⟨g (MvPolynomial.X 0), ?_⟩
  let e : k[X] →ₐ[k] MvPolynomial (Fin 1) k := Polynomial.aeval (MvPolynomial.X 0)
  have he : Function.Surjective e := by
    rw [← AlgHom.range_eq_top]
    change (Polynomial.aeval (R := k) (MvPolynomial.X (R := k) (0 : Fin 1))).range = ⊤
    rw [← Algebra.adjoin_singleton_eq_range_aeval, ← MvPolynomial.adjoin_range_X, Set.range_unique]
    rfl
  have hcomp : Polynomial.aeval (R := k) (g (MvPolynomial.X 0)) = g.comp e := by
    apply Polynomial.algHom_ext
    simp [e]
  rw [hcomp]
  exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ he)

theorem aeval_injective_of_finite_of_not_isField : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] (y : A),
    (Polynomial.aeval (R := k) y).Finite → ¬ IsField A → Function.Injective (Polynomial.aeval (R := k) y) := by
  intro k A _ _ _ _ y hy hA
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  by_contra hne
  push_neg at hne
  obtain ⟨p, hp, hp0⟩ := hne
  have hyi : IsIntegral k y := (show IsAlgebraic k y from ⟨p, hp0, hp⟩).isIntegral
  set B : Subalgebra k A := (Polynomial.aeval (R := k) y).range with hB
  haveI : Algebra.IsIntegral k B := by
    constructor
    rintro ⟨z, q, rfl⟩
    have : IsIntegral k (Polynomial.aeval y q) := by
      rw [Polynomial.aeval_eq_sum_range]
      refine IsIntegral.sum _ fun i _ => ?_
      exact (hyi.pow i).smul _
    exact (isIntegral_algHom_iff B.val Subtype.val_injective).1 this
  haveI : Algebra.IsIntegral k A := by
    constructor
    intro x
    have hx : (Polynomial.aeval (R := k) y).toRingHom.IsIntegralElem x := hy.to_isIntegral x
    obtain ⟨f, hfm, hf⟩ := hx
    let φ : k[X] →+* B := (Polynomial.aeval (R := k) y).rangeRestrict.toRingHom
    have hxB : IsIntegral B x := by
      refine ⟨f.map φ, hfm.map φ, ?_⟩
      rw [Polynomial.eval₂_map]
      have e : (algebraMap B A).comp φ = (Polynomial.aeval (R := k) y).toRingHom := RingHom.ext fun q => rfl
      rw [e]
      exact hf
    exact isIntegral_trans x hxB
  exact hA ((Algebra.IsIntegral.isField_iff_isField (algebraMap k A).injective).1 (Field.toIsField k))

theorem exists_D_algebraMap_fractionRing_ne_zero : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [IsFunctionField k (FractionRing A)],
    ∃ a : A, D k (FractionRing A) (algebraMap A (FractionRing A) a) ≠ 0 := by
  intro k A _ _ _ _ _
  have hnt := kaehlerDifferential_nontrivial (k := k) (K := FractionRing A)
  by_contra h
  push_neg at h
  have hall : ∀ x : FractionRing A, D k (FractionRing A) x = 0 := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, h a, h b]
    simp
  have htop : (⊤ : Submodule (FractionRing A) Ω[FractionRing A⁄k]) = ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    rintro _ ⟨x, rfl⟩
    exact hall x
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[FractionRing A⁄k])
  have hmem : ω ∈ (⊥ : Submodule (FractionRing A) Ω[FractionRing A⁄k]) := htop ▸ Submodule.mem_top
  exact hω ((Submodule.mem_bot _).1 hmem)

theorem isFunctionField_fractionRing_of_ringKrullDim_eq_one (k A : Type) [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (hR : ringKrullDim A = 1) :
    IsFunctionField k (FractionRing A) := by
  have htrA : Algebra.trdeg k A = 1 := by
    obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
    have hs := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_of_normalization k g hg hfin.to_isIntegral
    rw [hR] at hs
    have hs1 : s = 1 := by exact_mod_cast hs.symm
    subst hs1
    rw [GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_normalization k g hg hfin.to_isIntegral]
    simp
  have htr : Algebra.trdeg k (FractionRing A) = 1 := by
    have : FaithfulSMul A (FractionRing A) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective A _)
    have : Algebra.IsAlgebraic A (FractionRing A) :=
      IsLocalization.isAlgebraic (FractionRing A) (nonZeroDivisors A)
    rw [← trdeg_add_eq k A (A := FractionRing A), htrA, trdeg_eq_zero (R := A) (A := FractionRing A),
      add_zero]
  have : Algebra.Transcendental k (FractionRing A) := by
    rw [← trdeg_ne_zero_iff, htr]
    exact one_ne_zero
  obtain ⟨x, hx⟩ := Algebra.Transcendental.transcendental (R := k) (A := FractionRing A)
  refine ⟨x, hx, ?_⟩
  have hbx : IsTranscendenceBasis k ((↑) : ({x} : Set (FractionRing A)) → FractionRing A) :=
    AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite
      ((algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set (FractionRing A)))).2 hx)
      (by rw [htr, Cardinal.mk_singleton])
  have halg := hbx.isAlgebraic_field
  rw [Subtype.range_coe] at halg
  have : Algebra.EssFiniteType A (FractionRing A) :=
    Algebra.EssFiniteType.of_isLocalization (FractionRing A) (nonZeroDivisors A)
  have : Algebra.EssFiniteType k (FractionRing A) := Algebra.EssFiniteType.comp k A (FractionRing A)
  have : Algebra.EssFiniteType (IntermediateField.adjoin k {x}) (FractionRing A) :=
    Algebra.EssFiniteType.of_comp k _ (FractionRing A)
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

theorem exists_separable_normalisation_reduced_fibres : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A], ¬ IsField A → ∃ y : A, (Polynomial.aeval (R := k) y).Finite ∧ ∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → y - algebraMap k A α ∉ Q ^ 2 := by
  intro k A _ _ _ _ _ _ hA
  have hdim : ringKrullDim A = 1 := ringKrullDim_eq_one_of_isDedekindDomain_of_not_isField A hA
  haveI : IsFunctionField k (FractionRing A) :=
    isFunctionField_fractionRing_of_ringKrullDim_eq_one k A hdim
  obtain ⟨t, ht⟩ := exists_aeval_finite_of_ringKrullDim_eq_one k A hdim
  obtain ⟨a, ha⟩ := exists_D_algebraMap_fractionRing_ne_zero k A
  have key : ∃ y : A, (Polynomial.aeval (R := k) y).Finite ∧
      D k (FractionRing A) (algebraMap A (FractionRing A) y) ≠ 0 := by
    by_cases hD : D k (FractionRing A) (algebraMap A (FractionRing A) t) = 0
    · obtain ⟨M, hM⟩ := GlobalTheory.T.noether_normalization_finite_aeval_pow_add k A t a ht
      refine ⟨t ^ M + a, hM, ?_⟩
      rw [map_add (f := _), map_pow, map_add (f := _), Derivation.leibniz_pow, hD, smul_zero, smul_zero, zero_add]
      exact ha
    · exact ⟨t, ht, hD⟩
  obtain ⟨y, hy, hDy⟩ := key
  haveI := isSeparable_of_D_ne_zero hDy
  exact ⟨y, hy, GlobalTheory.T.reduced_fibres_almost_all_of_separable_dedekind_curve k A y hy (aeval_injective_of_finite_of_not_isField k A y hy hA) this⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDivisionPointNeZero
section
open ReciprocityTheory.PTheta Complex Matrix

namespace GlobalTheory.ThetaDivisionPoints

theorem theta_add_int_div {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm) {N : ℕ}
    (hN : (N : ℂ) ≠ 0) (a : Fin g → ℝ) (z : Fin g → ℂ) (m : Fin g → ℤ) :
    theta a 0 ((N : ℂ) • (z + (N : ℂ)⁻¹ • ofIntVec m)) ((N : ℂ) • τ) =
      eC (ofRealVec a ⬝ᵥ ofIntVec m) * theta a 0 ((N : ℂ) • z) ((N : ℂ) • τ) := by
  have h := thetaQuasiPeriod_holds (Fin g) a 0 ((N : ℂ) • z) ((N : ℂ) • τ) 0 m (hτ.smul _)
  rw [ofIntVec_zero, mulVec_zero, add_zero] at h
  rw [smul_add, smul_smul, mul_inv_cancel₀ hN, one_smul, h]
  congr 1
  simp [autFactor, ofIntVec_zero, eC_zero]

theorem theta_add_tau_div {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm) {N : ℕ}
    (hN : (N : ℂ) ≠ 0) (a : Fin g → ℝ) (z : Fin g → ℂ) (n : Fin g → ℤ) :
    ∃ u : ℂ, u ≠ 0 ∧ theta a 0 ((N : ℂ) • (z + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n)) ((N : ℂ) • τ) =
      u * theta (a + fun i => (n i : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) := by
  have h := thetaRealTransl_holds (Fin g) a 0 (fun i => (n i : ℝ) / N) 0 ((N : ℂ) • z)
    ((N : ℂ) • τ) (hτ.smul _)
  have e0 : ofRealVec (0 : Fin g → ℝ) = 0 := by ext i; simp [ofRealVec]
  have e1 : ofRealVec (fun i => (n i : ℝ) / N) = (N : ℂ)⁻¹ • ofIntVec n := by
    ext i; simp [ofRealVec, ofIntVec, div_eq_inv_mul]
  have e2 : ((N : ℂ) • τ) *ᵥ ((N : ℂ)⁻¹ • ofIntVec n) = (N : ℂ) • (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n := by
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul]
  rw [e0, add_zero, add_zero (0 : Fin g → ℝ)] at h
  rw [smul_add, ← e2, ← e1]
  exact ⟨_, Complex.exp_ne_zero _, h⟩

noncomputable def intChar {g : ℕ} (N : ℕ) (c : Fin g → Fin N) : Multiplicative (Fin g → ℤ) →* ℂ where
  toFun m := eC (ofRealVec (fun i => ((c i : ℕ) : ℝ) / N) ⬝ᵥ ofIntVec m.toAdd)
  map_one' := by simp [ofIntVec_zero, eC_zero]
  map_mul' m m' := by rw [toAdd_mul, ofIntVec_add, dotProduct_add, eC_add]

theorem intChar_injective {g : ℕ} {N : ℕ} (hN : N ≠ 0) :
    Function.Injective (intChar (g := g) N) := by
  intro c c' h
  funext i
  have key : ∀ d : Fin g → Fin N, intChar N d (Multiplicative.ofAdd (Pi.single i 1)) =
      cexp (2 * Real.pi * I / N) ^ (d i : ℕ) := by
    intro d
    change eC (ofRealVec (fun i => ((d i : ℕ) : ℝ) / N) ⬝ᵥ ofIntVec (Pi.single i 1)) = _
    rw [GlobalTheory.ThetaSpan.ofIntVec_single, dotProduct_single_one, ← Complex.exp_nat_mul, eC]
    congr 1
    simp only [ofRealVec]
    push_cast
    ring
  have h1 := key c
  rw [h, key c'] at h1
  exact Fin.ext ((Complex.isPrimitiveRoot_exp N hN).pow_inj (c i).2 (c' i).2 h1.symm)

theorem mem_span_of_laws {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) {N : ℕ}
    (hN : 1 ≤ N) {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f ∧
      (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) ∧
      ∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) =
        eC (-(τ j j) / 2) ^ N * cexp (-(2 * Real.pi * I) * N * z j) * f z) :
    f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
      theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) := by
  have f4 := @GlobalTheory.fourierCoeff_unitCube_translate_of_entire_periodic
  have f5 := @GlobalTheory.entire_periodic_eq_zero_of_fourierCoeff_eq_zero f4
  have hdim := @GlobalTheory.ClassicalTheta.card_le_pow_of_linearIndependent f4 f5
  obtain ⟨hlev, hli⟩ := classicalTheta_level_and_linearIndependent' g τ hτ N hN
  by_contra hnot
  have hopt := hli.option hnot
  have hcard : Fintype.card (Option (Fin g → Fin N)) = N ^ g + 1 := by simp
  let e := (Fintype.equivFinOfCardEq hcard).symm
  have hli' := hopt.comp e e.injective
  have := hdim g N τ (fun j => eC (-(τ j j) / 2)) hN (fun j => Complex.exp_ne_zero _)
    (N ^ g + 1) _ (fun k => ?_) hli'
  · omega
  · simp only [Function.comp_apply]
    rcases e k with _ | c
    · exact hf
    · exact ⟨(hlev c).1, GlobalTheory.ThetaSpan.laws_of_level τ N _ (hlev c).2⟩

theorem exists_theta_ne_zero {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g))
    {N : ℕ} (hN : 2 ≤ N) (z : Fin g → ℂ) : ∃ c : Fin g → Fin N,
      theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 := by
  have f8 := @GlobalTheory.riemannTheta_level_one_ne_zero classicalTheta_level_and_linearIndependent'
  obtain ⟨f, hf, hz⟩ := GlobalTheory.exists_level_apply_ne_zero_of_two_le f8 g τ hτ N hN z
  have hs := mem_span_of_laws hτ (by omega : 1 ≤ N) ⟨hf.1, GlobalTheory.ThetaSpan.laws_of_level τ N f hf.2⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hs
  by_contra hcon
  push Not at hcon
  apply hz
  rw [← ha]
  simp [Finset.sum_apply, hcon]

theorem exists_division_point_ne_zero :
    ∀ (g N : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (β : Fin g → ℂ) (f : (Fin g → ℂ) → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → 2 ≤ N → (∀ j, β j ≠ 0) → Differentiable ℂ f → f ≠ 0 → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → (∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) = β j * cexp (-(2 * Real.pi * I) * N * z j) * f z) → ∃ m n : Fin g → ℤ, f ((N : ℂ)⁻¹ • ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) ≠ 0 := by
  intro g N τ β f hs hp hN hβ hd hf0 hper hlaw
  have hτ : τ ∈ SiegelH (Fin g) := ⟨hs, hp⟩
  have hN0 : N ≠ 0 := by omega
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let w : Fin g → ℂ := fun j => Complex.log (β j) / (2 * Real.pi * I * N) + τ j j / 2
  have hw : ∀ j, β j * cexp (-(2 * Real.pi * I) * N * w j) = eC (-(τ j j) / 2) ^ N := by
    intro j
    rw [eC, ← Complex.exp_nat_mul]
    conv_lhs => rw [← Complex.exp_log (hβ j), ← Complex.exp_add]
    congr 1
    simp only [w]
    field_simp
    ring
  have hF := mem_span_of_laws (f := fun z => f (z + w)) hτ (by omega : 1 ≤ N)
    ⟨hd.comp (by fun_prop), fun i z => by
      rw [add_right_comm, hper], fun j z => by
      rw [add_right_comm, hlaw, ← hw j, Pi.add_apply, mul_add, Complex.exp_add]
      ring⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hF
  obtain ⟨c₀, hc₀⟩ : ∃ c, a c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hf0
    funext z
    have := congrFun ha (z - w)
    simpa [hcon] using this.symm
  by_contra hcon
  push Not at hcon
  have hvan : ∀ n : Fin g → ℤ, theta (fun i => ((c₀ i : ℕ) : ℝ) / N) 0
      ((N : ℂ) • (-w + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n)) ((N : ℂ) • τ) = 0 := by
    intro n
    have hli := (linearIndependent_monoidHom (Multiplicative (Fin g → ℤ)) ℂ).comp _
      (intChar_injective (g := g) hN0)
    have := Fintype.linearIndependent_iff.1 hli
      (fun c => a c * theta (fun i => ((c i : ℕ) : ℝ) / N) 0
        ((N : ℂ) • (-w + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n)) ((N : ℂ) • τ)) (by
        funext m
        have h1 := congrFun ha (-w + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n + (N : ℂ)⁻¹ • ofIntVec m.toAdd)
        have h2 := hcon m.toAdd n
        have e : -w + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n + (N : ℂ)⁻¹ • ofIntVec m.toAdd + w =
            (N : ℂ)⁻¹ • ((fun i => (m.toAdd i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) := by
          rw [smul_add]
          change _ = (N : ℂ)⁻¹ • ofIntVec m.toAdd + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n
          abel
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
        rw [e, h2] at h1
        rw [Pi.zero_apply, ← h1]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [theta_add_int_div hs hNC, mul_assoc, mul_comm (eC _)]
        rfl) c₀
    exact (mul_eq_zero.1 this).resolve_left hc₀
  obtain ⟨c, hc⟩ := exists_theta_ne_zero hτ hN (-w)
  obtain ⟨u, hu, h⟩ := theta_add_tau_div hs hNC (fun i => ((c₀ i : ℕ) : ℝ) / N) (-w)
    (fun i => ((c i : ℕ) : ℤ) - ((c₀ i : ℕ) : ℤ))
  rw [hvan] at h
  have e : ((fun i => ((c₀ i : ℕ) : ℝ) / N) +
      fun i => ((((c i : ℕ) : ℤ) - ((c₀ i : ℕ) : ℤ) : ℤ) : ℝ) / N) =
      fun i => ((c i : ℕ) : ℝ) / N := by
    funext i
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [e] at h
  exact mul_ne_zero hu hc h.symm

end GlobalTheory.ThetaDivisionPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateInCell
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem finite_det_line_zero {F E : Type} [Field F] [Field E] [Algebra F E] {ν : Type} [Fintype ν] [DecidableEq ν]
    (A B : Matrix ν ν E) (r₀ : F) (h : (A + algebraMap F E r₀ • B).det ≠ 0) :
    {r : F | (A + algebraMap F E r • B).det = 0}.Finite := by
  set M : Matrix ν ν (Polynomial E) := A.map Polynomial.C + (Polynomial.X : Polynomial E) • B.map Polynomial.C with hM
  have hev : ∀ x : E, M.det.eval x = (A + x • B).det := by
    intro x
    have h1 := RingHom.map_det (Polynomial.evalRingHom x) M
    rw [Polynomial.coe_evalRingHom] at h1
    rw [h1]
    congr 1
    ext i j
    simp [hM]
    ring
  have hp : M.det ≠ 0 := by
    intro h0
    apply h
    rw [← hev, h0, Polynomial.eval_zero]
  have hfin := Polynomial.finite_setOfPred_isRoot hp
  refine (hfin.preimage (f := algebraMap F E) (algebraMap F E).injective.injOn).subset ?_
  intro r hr
  change M.det.eval _ = 0
  rw [hev]
  exact hr

theorem exists_herm_transversal (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
    (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (s : Finset (UG c (stdJ ν E))) :
    ∃ t : Matrix ν ν E, (t.map c)ᵀ = t ∧ ∀ g ∈ s, ((mat c g).toBlocks₂₁ + (mat c g).toBlocks₂₂ * t).det ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by ext i j; simp, by simp⟩
  | insert g s _ ih =>
    obtain ⟨t₀, ht₀, h₀⟩ := ih
    obtain ⟨t₁, ht₁, h₁⟩ := _root_.GlobalTheory.KSp.exists_herm_transverse F E c δ hE ν g
    have key : ∀ k ∈ insert g s, {r : F | (((mat c k).toBlocks₂₁ + (mat c k).toBlocks₂₂ * t₀) +
        algebraMap F E r • ((mat c k).toBlocks₂₂ * (t₁ - t₀))).det = 0}.Finite := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · refine finite_det_line_zero _ _ 1 ?_
        rw [map_one, one_smul, add_assoc, ← Matrix.mul_add, add_sub_cancel]
        exact h₁
      · refine finite_det_line_zero _ _ 0 ?_
        rw [map_zero, zero_smul, add_zero]
        exact h₀ k hk
    have hfin := Set.Finite.biUnion (insert g s).finite_toSet key
    obtain ⟨r, hr⟩ := hfin.exists_notMem
    refine ⟨t₀ + algebraMap F E r • (t₁ - t₀), ?_, ?_⟩
    · ext i j
      have e₀ : c (t₀ j i) = t₀ i j := congrFun (congrFun ht₀ i) j
      have e₁ : c (t₁ j i) = t₁ i j := congrFun (congrFun ht₁ i) j
      simp [e₀, e₁]
    · intro k hk h0
      apply hr
      refine Set.mem_biUnion (Finset.mem_coe.mpr hk) ?_
      rw [Matrix.mul_add, Matrix.mul_smul, ← add_assoc] at h0
      exact h0

theorem exists_translate_inCell : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (s : Finset (UG c (stdJ ν E))),
    ∃ u : UG c (stdJ ν E), ∀ g ∈ s, InCell c (g * u) := by
  intro F _ _ E _ _ c δ hE ν _ _ s
  obtain ⟨t, ht, h⟩ := exists_herm_transversal F E c δ hE ν s
  let u : UG c (stdJ ν E) :=
    ⟨⟨fromBlocks 1 0 t 1, fromBlocks 1 0 (-t) 1, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩, by
      rw [mem_UG_iff]
      have h0 : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
      have h1 : (1 : Matrix ν ν E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
      simp [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, h0, h1, ht]⟩
  refine ⟨u, fun g hg => (_root_.GlobalTheory.KSp.inCell_iff_det_ne_zero F E c δ hE ν _).mpr ?_⟩
  have e : mat c (g * u) = mat c g * fromBlocks 1 0 t 1 := rfl
  rw [e, ← fromBlocks_toBlocks (mat c g), fromBlocks_multiply, toBlocks_fromBlocks₂₁, Matrix.mul_one]
  exact h g hg

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIntegralClosureOverGenericFibreOfEtale
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

theorem finite_closure (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Algebra A R] [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D] :
    (letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
     Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R D)) := by
  letI iRD : Algebra R D := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GlobalTheory.LocAcyc.GenFib A R) D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  haveI : Module.Flat R (GlobalTheory.LocAcyc.GenFib A R) := IsLocalization.flat _ M
  haveI : Module.Flat R D := Module.Flat.trans R (GlobalTheory.LocAcyc.GenFib A R) D
  haveI : Algebra.FormallyEtale R (GlobalTheory.LocAcyc.GenFib A R) := Algebra.FormallyEtale.of_isLocalization M
  haveI : Algebra.FormallyEtale R D := Algebra.FormallyEtale.comp R (GlobalTheory.LocAcyc.GenFib A R) D
  haveI : Algebra.EssFiniteType R (GlobalTheory.LocAcyc.GenFib A R) := Algebra.EssFiniteType.of_isLocalization _ M
  haveI : Algebra.EssFiniteType R D := Algebra.EssFiniteType.comp R (GlobalTheory.LocAcyc.GenFib A R) D
  have h1 : Module.Finite R (integralClosure R (R ⊗[R] D)) :=
    GlobalTheory.RootFibre.finite_integralClosure R D R
  have e := AlgEquiv.mapIntegralClosure (Algebra.TensorProduct.lid R D)
  have h2 : Module.Finite R (integralClosure R D) := Module.Finite.equiv e.toLinearEquiv
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  let f : integralClosure R D ≃ₗ[R] GlobalTheory.KeyOriginNoeth.closure A R D :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        apply Subtype.ext
        show r • x.1 = (baseHom A R D r) * x.1
        rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Finite.equiv f

end GlobalTheory.KeyOriginNoeth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLIsCharacterStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_isCharacter : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsChar ℂ ℂ α → IsChar ℂ ℂ β → IsChar ℂ ℂ (hc a b α β n) := by
  first | (exact @GlobalTheory.Shin.HCChar.hc_isChar) | (exact GlobalTheory.Shin.HCChar.hc_isChar) | (intros; apply GlobalTheory.Shin.HCChar.hc_isChar  <;> assumption)
end

