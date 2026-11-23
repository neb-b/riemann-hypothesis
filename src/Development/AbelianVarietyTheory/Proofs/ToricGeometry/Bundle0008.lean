module

public import Mathlib
public import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
public import ReciprocityTheory.ThetaQuasiPeriods.Transl
public import ReciprocityTheory.ThetaQuasiPeriods.Change
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsConnectedPrincipalOpen
section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

noncomputable def evalPair {d : ℕ} (z : (Fin d → ℂ) × ℂ) :
    Polynomial (MvPolynomial (Fin d) ℂ) →+* ℂ :=
  Polynomial.eval₂RingHom (MvPolynomial.eval z.1) z.2

theorem evalPair_eq {d : ℕ} (z : (Fin d → ℂ) × ℂ) (r : Polynomial (MvPolynomial (Fin d) ℂ)) :
    evalPair z r = (r.map (MvPolynomial.eval z.1)).eval z.2 := by
  simp [evalPair, Polynomial.eval_map]

@[simp] theorem evalPair_C {d : ℕ} (z : (Fin d → ℂ) × ℂ) (s : MvPolynomial (Fin d) ℂ) :
    evalPair z (Polynomial.C s) = MvPolynomial.eval z.1 s := by
  simp [evalPair]

@[simp] theorem evalPair_X {d : ℕ} (z : (Fin d → ℂ) × ℂ) :
    evalPair z Polynomial.X = z.2 := by
  simp [evalPair]

theorem continuous_evalPair {d : ℕ} (r : Polynomial (MvPolynomial (Fin d) ℂ)) :
    Continuous fun z : (Fin d → ℂ) × ℂ => evalPair z r := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | monomial n s =>
    simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, evalPair_C, evalPair_X]
    exact ((MvPolynomial.continuous_eval s).comp continuous_fst).mul (continuous_snd.pow n)

theorem points_eq_image_hypersurface {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}
    (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (q q' : MvPolynomial (Fin d) ℂ)
    (hp : ∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r)
    (r : A → Polynomial (MvPolynomial (Fin d) ℂ))
    (hr : ∀ b, j q * b = (r b).eval₂ j.toRingHom a) :
    {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x (j (q * q')) ≠ 0} =
      (fun (z : (Fin d → ℂ) × ℂ) (b : A) => evalPair z (r b) / MvPolynomial.eval z.1 q) ''
        {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 (q * q') ≠ 0 ∧
          (p.map (MvPolynomial.eval z.1)).eval z.2 = 0} := by
  set E : Polynomial (MvPolynomial (Fin d) ℂ) →+* A :=
    Polynomial.eval₂RingHom j.toRingHom a with hE
  have hEr : ∀ b, E (r b) = j q * b := fun b => (hr b).symm
  have hEC : ∀ s, E (Polynomial.C s) = j s := fun s => by simp [hE]
  ext x
  constructor
  · rintro ⟨φ, rfl, hφ⟩
    let z : (Fin d → ℂ) × ℂ := (fun i => φ (j (MvPolynomial.X i)), φ a)
    have h1 : ∀ s, φ (j s) = MvPolynomial.eval z.1 s := by
      intro s
      induction s using MvPolynomial.induction_on with
      | C c =>
        have : (MvPolynomial.C c : MvPolynomial (Fin d) ℂ) = algebraMap ℂ _ c := rfl
        rw [MvPolynomial.eval_C, this, AlgHom.commutes, AlgHom.commutes]; rfl
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
      | mul_X s i hs => simp only [map_mul, hs, MvPolynomial.eval_X, z]
    have h2 : ∀ s, φ (E s) = evalPair z s := by
      intro s
      induction s using Polynomial.induction_on' with
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
      | monomial n s =>
        have hX : E Polynomial.X = a := by simp [hE]
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_mul, map_pow, map_pow,
          map_pow, evalPair_C, evalPair_X, hEC, h1, hX]
    have hne : MvPolynomial.eval z.1 (q * q') ≠ 0 := by rwa [← h1]
    have hq : MvPolynomial.eval z.1 q ≠ 0 := by
      rw [map_mul] at hne; exact left_ne_zero_of_mul hne
    refine ⟨z, ⟨hne, ?_⟩, ?_⟩
    · have : E p = 0 := (hp p).2 dvd_rfl
      rw [← evalPair_eq, ← h2, this, map_zero]
    · funext b
      simp only
      rw [← h2, hEr, map_mul, h1]
      field_simp
  · rintro ⟨z, ⟨hne, hz⟩, rfl⟩
    have hq : MvPolynomial.eval z.1 q ≠ 0 := by
      rw [map_mul] at hne; exact left_ne_zero_of_mul hne
    rw [← evalPair_eq] at hz
    have key : ∀ s t, E s = E t → evalPair z s = evalPair z t := by
      intro s t hst
      have h0 : E (s - t) = 0 := by rw [map_sub, hst, sub_self]
      obtain ⟨u, hu⟩ := (hp (s - t)).1 h0
      rw [← sub_eq_zero, ← map_sub, hu, map_mul, hz, zero_mul]
    have hj : ∀ s, evalPair z (r (j s)) / MvPolynomial.eval z.1 q = MvPolynomial.eval z.1 s := by
      intro s
      rw [key (r (j s)) (Polynomial.C (q * s)) (by rw [hEr, hEC, map_mul]), evalPair_C, map_mul]
      field_simp
    let φ : A →ₐ[ℂ] ℂ :=
      { toFun := fun b => evalPair z (r b) / MvPolynomial.eval z.1 q
        map_one' := by simpa using hj 1
        map_zero' := by simpa using hj 0
        map_mul' := by
          intro b c
          have := key (r (b * c) * Polynomial.C q) (r b * r c)
            (by simp only [map_mul, hEr, hEC]; ring)
          simp only [map_mul, evalPair_C] at this
          field_simp
          exact this
        map_add' := by
          intro b c
          have := key (r (b + c)) (r b + r c) (by simp only [map_add (f := _), hEr]; ring)
          rw [this, map_add (f := _), add_div]
        commutes' := by
          intro c
          have := hj (algebraMap ℂ _ c)
          rw [AlgHom.commutes] at this
          rw [this]
          simp }
    refine ⟨φ, rfl, ?_⟩
    simp only
    rw [hj]
    exact hne

theorem exists_isConnected_principalOpen :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a) → (∀ (d : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), p.Monic → Irreducible p → q ≠ 0 → (∀ x y, MvPolynomial.eval x q ≠ 0 → (p.map (MvPolynomial.eval x)).eval y = 0 → (p.map (MvPolynomial.eval x)).derivative.eval y ≠ 0) → IsConnected {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}) → (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → ∃ h : A, h ≠ 0 ∧ IsConnected {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x (h * f) ≠ 0}) := by
  intro H1 H2 A _ _ _ _ f hf
  obtain ⟨d, j, a, p, q, -, hinj, hfin, hmon, hirr, hp, hq, hspan, hr⟩ := H1 A
  choose r hr using hr
  obtain ⟨q', hq', f', hf'⟩ : ∃ q' : MvPolynomial (Fin d) ℂ, q' ≠ 0 ∧ f ∣ j q' := by
    letI : Algebra (MvPolynomial (Fin d) ℂ) A := j.toRingHom.toAlgebra
    haveI : Module.Finite (MvPolynomial (Fin d) ℂ) A := hfin
    have hint : IsIntegral (MvPolynomial (Fin d) ℂ) f := Algebra.IsIntegral.isIntegral f
    exact hint.isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)
  have hmul : j q * f' * f = j (q * q') := by rw [map_mul, hf']; ring
  have hqq : q * q' ≠ 0 := mul_ne_zero hq hq'
  refine ⟨j q * f', ?_, ?_⟩
  · intro h0
    rw [h0, zero_mul] at hmul
    exact hqq (hinj (by rw [← hmul, map_zero]))
  · rw [hmul, points_eq_image_hypersurface j a p q q' hp r hr]
    refine (H2 d p (q * q') hmon hirr hqq ?_).image _ ?_
    · intro x y hx hy hd
      obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hspan
      have h := congrArg (evalPair (x, y)) huv
      rw [Polynomial.derivative_map] at hd
      simp only [map_add (f := _), map_mul, evalPair_C] at h
      rw [evalPair_eq _ p, evalPair_eq _ p.derivative, hy, hd, mul_zero, mul_zero, add_zero] at h
      rw [map_mul, ← h, zero_mul] at hx
      exact hx rfl
    · refine continuousOn_pi.2 fun b => ContinuousOn.div (continuous_evalPair _).continuousOn
        ((MvPolynomial.continuous_eval q).comp continuous_fst).continuousOn ?_
      intro z hz
      have := hz.1
      rw [map_mul] at this
      exact left_ne_zero_of_mul this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsPrimitiveElementDiscriminantMultiple
section
namespace GlobalTheory.NoetherPrimitive

open Polynomial
open scoped nonZeroDivisors

theorem exists_map_eq_C_mul {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (f : K[X]) :
    ∃ s : R, s ≠ 0 ∧ ∃ g : R[X], g.map (algebraMap R K) = C (algebraMap R K s) * f := by
  obtain ⟨s, hs, h⟩ := IsLocalization.integerNormalization_spec R⁰ f
  refine ⟨s, nonZeroDivisors.ne_zero hs, IsLocalization.integerNormalization R⁰ f, ?_⟩
  rw [h, ← smul_eq_C_mul, algebraMap_smul]

theorem exists_C_mem_span {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (p : R[X]) (hp : (p.map (algebraMap R K)).Separable) :
    ∃ q : R, q ≠ 0 ∧ C q ∈ Ideal.span {p, p.derivative} := by
  obtain ⟨u, v, huv⟩ := hp
  obtain ⟨s, hs, U, hU⟩ := exists_map_eq_C_mul (R := R) u
  obtain ⟨t, ht, V, hV⟩ := exists_map_eq_C_mul (R := R) v
  refine ⟨s * t, mul_ne_zero hs ht, Ideal.mem_span_pair.2 ⟨C t * U, C s * V, ?_⟩⟩
  apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
  rw [derivative_map] at huv
  simp only [Polynomial.map_add (f := _), Polynomial.map_mul, map_C, hU, hV, map_mul]
  linear_combination (C (algebraMap R K s) * C (algebraMap R K t)) * huv

theorem exists_common_denominator {R A : Type*} [CommRing R] [IsDomain R] [CommRing A]
    [Algebra R A] [Module.Finite R A] (a : A)
    (h : ∀ b : A, ∃ s : R, s ≠ 0 ∧ ∃ r : R[X], algebraMap R A s * b = aeval a r) :
    ∃ s : R, s ≠ 0 ∧ ∀ b : A, ∃ r : R[X], algebraMap R A s * b = aeval a r := by
  first
  | exact @_root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator
  | exact _root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator
  | (apply _root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator ..)

theorem exists_primitive_element_discriminant_multiple (R A K L : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Module.Finite R A]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra A L]
    [IsFractionRing A L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R A L] :
    ∃ (a : A) (q : R), q ≠ 0 ∧ C q ∈ Ideal.span {minpoly R a, (minpoly R a).derivative} ∧
      ∀ b : A, ∃ r : R[X], algebraMap R A q * b = aeval a r := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A R⁰) L := inferInstance
  haveI : Module.Finite K L := Module.Finite.of_isLocalization R A R⁰
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  obtain ⟨⟨a, ⟨_, t, ht, rfl⟩⟩, hat⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid A R⁰) α
  have ht' : algebraMap R K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (nonZeroDivisors.ne_zero ht)
  have hat' : α = algebraMap K L (algebraMap R K t)⁻¹ * algebraMap A L a := by
    simp only at hat
    rw [← hat, ← IsScalarTower.algebraMap_apply R A L, IsScalarTower.algebraMap_apply R K L,
      mul_left_comm, ← map_mul, inv_mul_cancel₀ ht', map_one, mul_one]
  have hint : IsIntegral R a := Algebra.IsIntegral.isIntegral a
  have htop : Algebra.adjoin K {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α), hα, IntermediateField.top_toSubalgebra]
  obtain ⟨q₁, hq₁, h₁⟩ := exists_common_denominator (R := R) a fun b => by
    have hb : algebraMap A L b ∈ Algebra.adjoin K {α} := htop ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
    obtain ⟨f, hf⟩ := hb
    obtain ⟨s, hs, g, hg⟩ := exists_map_eq_C_mul (R := R) (f.comp (C (algebraMap R K t)⁻¹ * X))
    refine ⟨s, hs, g, IsFractionRing.injective A L ?_⟩
    rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap K, hg, map_mul, map_mul, aeval_C,
      aeval_comp, map_mul, aeval_C, aeval_X, ← hat', ← hf, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
    rfl
  obtain ⟨q₂, hq₂, h₂⟩ := exists_C_mem_span (K := K) (minpoly R a) (by
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L hint]
    exact Algebra.IsSeparable.isSeparable K _)
  refine ⟨a, q₂ * q₁, mul_ne_zero hq₂ hq₁, ?_, fun b => ?_⟩
  · rw [C_mul]; exact Ideal.mul_mem_right _ _ h₂
  · obtain ⟨r, hr⟩ := h₁ b
    exact ⟨C q₂ * r, by rw [map_mul, map_mul, aeval_C, mul_assoc, hr]⟩

theorem exists_primitive (R A : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CharZero R] [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Module.Finite R A] :
    ∃ (a : A) (q : R), q ≠ 0 ∧ C q ∈ Ideal.span {minpoly R a, (minpoly R a).derivative} ∧
      ∀ b : A, ∃ r : R[X], algebraMap R A q * b = aeval a r := by
  letI : Algebra (FractionRing R) (FractionRing A) := FractionRing.liftAlgebra R (FractionRing A)
  exact exists_primitive_element_discriminant_multiple R A (FractionRing R) (FractionRing A)

end GlobalTheory.NoetherPrimitive

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

theorem GlobalTheory.noetherNormalization_primitive :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a) := by
  intro A _ _ _ _
  obtain ⟨d, j, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ A
  letI : Algebra (MvPolynomial (Fin d) ℂ) A := j.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin d) ℂ) A := hfin
  have hinj' : Function.Injective (algebraMap (MvPolynomial (Fin d) ℂ) A) := hinj
  haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj'
  obtain ⟨a, q, hq, hq₁, hq₂⟩ := GlobalTheory.NoetherPrimitive.exists_primitive (MvPolynomial (Fin d) ℂ) A
  have hint : IsIntegral (MvPolynomial (Fin d) ℂ) a := Algebra.IsIntegral.isIntegral a
  refine ⟨d, j, a, minpoly _ a, q, ?_, hinj, hfin, minpoly.monic hint, minpoly.irreducible hint,
    fun r => minpoly.isIntegrallyClosed_dvd_iff hint r, hq, hq₁, hq₂⟩
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj',
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.FiniteOfIsIntegralOfBirationalOfPresentation
section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

theorem finite_of_isIntegral_of_birational_of_finite_over_normal
    (R A B : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [CharZero R] [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra R A] [FaithfulSMul R A] [Module.Finite R A]
    [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (hb : ∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) :
    Module.Finite A B := by
  letI : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let L := FractionRing B
  haveI : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply A B L]; rfl
  have hAB : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A B L]; exact hBL.comp hAB

  haveI : IsFractionRing A L := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · intro y
      exact IsUnit.mk0 _ ((map_ne_zero_iff _ hAL).mpr (nonZeroDivisors.ne_zero y.2))
    · intro z
      obtain ⟨⟨x, y⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors B) z
      obtain ⟨a₁, c₁, hc₁, h₁⟩ := hb x
      obtain ⟨a₂, c₂, hc₂, h₂⟩ := hb (y : B)
      have hy : (y : B) ≠ 0 := nonZeroDivisors.ne_zero y.2
      have ha₂ : a₂ ≠ 0 := by
        intro h0
        rw [h0, map_zero] at h₂
        exact mul_ne_zero ((map_ne_zero_iff _ hAB).mpr hc₂) hy h₂
      refine ⟨⟨a₁ * c₂, ⟨c₁ * a₂, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hc₁ ha₂)⟩⟩, ?_⟩
      simp only [IsScalarTower.algebraMap_apply A B L, map_mul, ← h₁, ← h₂]
      simp only [map_mul] at hz ⊢
      rw [← hz]; ring
    · intro x y hxy
      exact ⟨1, by rw [hAL hxy]⟩
  haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr (by
    rw [IsScalarTower.algebraMap_eq R A L]
    exact hAL.comp (FaithfulSMul.algebraMap_injective R A))
  let K := FractionRing R
  letI : Algebra K L := FractionRing.liftAlgebra R L
  haveI : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  haveI : Module.Finite K L := Module.Finite.of_isLocalization R A (nonZeroDivisors R)
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  haveI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.trans A
  let f : B →ₐ[R] integralClosure R L :=
    (IsScalarTower.toAlgHom R B L).codRestrict (integralClosure R L)
      (fun b => (Algebra.IsIntegral.isIntegral (R := R) b).map (IsScalarTower.toAlgHom R B L))
  have hf : Function.Injective f.toLinearMap := fun x y h =>
    hBL (congrArg Subtype.val h)
  haveI : IsNoetherian R (integralClosure R L) := isNoetherian_of_isNoetherianRing_of_finite _ _
  haveI : IsNoetherian R B := isNoetherian_of_injective f.toLinearMap hf
  haveI : Module.Finite R B := Module.IsNoetherian.finite R B
  exact Module.Finite.of_restrictScalars_finite R A B

theorem finite_of_isIntegral_of_birational_complex
    (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (hb : ∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) :
    Module.Finite A B := by
  obtain ⟨d, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ A
  letI : Algebra (MvPolynomial (Fin d) ℂ) A := g.toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hg
  haveI : Module.Finite (MvPolynomial (Fin d) ℂ) A := hfin
  exact finite_of_isIntegral_of_birational_of_finite_over_normal (MvPolynomial (Fin d) ℂ) A B hb

theorem finite_of_isIntegral_of_birational_of_presentation :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a) → (∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra ℂ A] [Algebra.FiniteType ℂ A] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B], (∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) → Module.Finite A B) := by
  intro _ A B _ _ _ _ _ _ _ _ _ hb
  exact finite_of_isIntegral_of_birational_complex A B hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsConnectedAndDenseComplHypersurface
section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

noncomputable def mvPolynomialOnLine {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (a b : Fin d → ℂ) :
    Polynomial ℂ :=
  MvPolynomial.aeval (fun i => Polynomial.C (a i) + Polynomial.C (b i - a i) * Polynomial.X) q

theorem eval_mvPolynomialOnLine {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (a b : Fin d → ℂ) (t : ℂ) :
    (mvPolynomialOnLine q a b).eval t = MvPolynomial.eval (a + t • (b - a)) q := by
  unfold mvPolynomialOnLine
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add p r hp hr => rw [map_add (f := _), Polynomial.eval_add, hp, hr, map_add (f := _)]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.eval_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    ring

theorem finite_zeros_on_line {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (a b : Fin d → ℂ)
    (hb : MvPolynomial.eval b q ≠ 0) :
    {t : ℂ | MvPolynomial.eval (a + t • (b - a)) q = 0}.Finite := by
  have hP : mvPolynomialOnLine q a b ≠ 0 := by
    intro h
    apply hb
    have := eval_mvPolynomialOnLine q a b 1
    simpa [h] using this.symm
  convert Polynomial.finite_setOfPred_isRoot hP using 1
  ext t
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, eval_mvPolynomialOnLine]

private theorem mvPolynomial_exists_eval_ne_zero {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (hq : q ≠ 0) :
    ∃ x : Fin d → ℂ, MvPolynomial.eval x q ≠ 0 := by
  by_contra h
  push Not at h
  exact hq (MvPolynomial.funext fun x => by simp [h x])

private theorem joinedIn_setOf_eval_ne_zero {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (a b : Fin d → ℂ)
    (ha : MvPolynomial.eval a q ≠ 0) (hb : MvPolynomial.eval b q ≠ 0) :
    JoinedIn {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} a b := by
  have hZ := finite_zeros_on_line q a b hb
  have hpc : IsPathConnected {t : ℂ | MvPolynomial.eval (a + t • (b - a)) q = 0}ᶜ :=
    hZ.countable.isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)
  have h0 : (0 : ℂ) ∈ {t : ℂ | MvPolynomial.eval (a + t • (b - a)) q = 0}ᶜ := by simpa using ha
  have h1 : (1 : ℂ) ∈ {t : ℂ | MvPolynomial.eval (a + t • (b - a)) q = 0}ᶜ := by simpa using hb
  have hf : Continuous fun t : ℂ => a + t • (b - a) := by fun_prop
  have hj := (hpc.joinedIn 0 h0 1 h1).map hf.continuousOn
  simp only [zero_smul, add_zero, one_smul, add_sub_cancel] at hj
  refine hj.mono ?_
  rintro _ ⟨t, ht, rfl⟩
  exact ht

theorem isConnected_and_dense_compl_hypersurface :
    (∀ (d : ℕ) (q : MvPolynomial (Fin d) ℂ), q ≠ 0 →
      IsConnected {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} ∧
        Dense {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0}) := by
  intro d q hq
  obtain ⟨b, hb⟩ := mvPolynomial_exists_eval_ne_zero q hq
  refine ⟨(isPathConnected_iff.2 ⟨⟨b, hb⟩, fun x hx y hy => joinedIn_setOf_eval_ne_zero q x y hx hy⟩).isConnected,
    fun x => ?_⟩
  have hf : Continuous fun t : ℂ => x + t • (b - x) := by fun_prop
  have hlim : Tendsto (fun t : ℂ => x + t • (b - x)) (𝓝[≠] (0 : ℂ)) (𝓝 x) := by
    have := hf.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine mem_closure_of_tendsto hlim ?_
  have hZ := finite_zeros_on_line q x b hb
  have hcl : IsClosed ({t : ℂ | MvPolynomial.eval (x + t • (b - x)) q = 0} \ {0}) :=
    (hZ.subset Set.sdiff_subset).isClosed
  have e1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      t ∉ ({t : ℂ | MvPolynomial.eval (x + t • (b - x)) q = 0} \ {0}) :=
    nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (by simp))
  have e2 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ≠ 0 := self_mem_nhdsWithin
  filter_upwards [e1, e2] with t ht1 ht2
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, not_and, not_not] at ht1
  show MvPolynomial.eval (x + t • (b - x)) q ≠ 0
  exact fun h => ht2 (ht1 h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsConnectedBasicOpenComplexPointsOfDense
section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

theorem isConnected_basicOpen_complexPoints_of_dense :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → ∃ h : A, h ≠ 0 ∧ IsConnected {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x (h * f) ≠ 0}) →
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x 1 ≠ 0} ⊆ closure {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x f ≠ 0}) →
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → IsConnected {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x f ≠ 0}) := by
  intro H1 H2 A _ _ _ _ f hf

  obtain ⟨h, hh, hconn⟩ := H1 A f hf
  have hhf : h * f ≠ 0 := mul_ne_zero hh hf

  apply hconn.subset_closure
  · rintro x ⟨φ, rfl, hx⟩
    refine ⟨φ, rfl, ?_⟩
    rw [map_mul] at hx
    exact right_ne_zero_of_mul hx
  · rintro x ⟨φ, rfl, -⟩
    exact H2 A (h * f) hhf ⟨φ, rfl, by simp⟩

end GlobalTheory
end

