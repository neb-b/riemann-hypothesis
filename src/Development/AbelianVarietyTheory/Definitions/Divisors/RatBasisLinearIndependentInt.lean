module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration

@[expose] public section

set_option autoImplicit false

noncomputable section

open DividedPowers

namespace GlobalTheory.PDA

variable {B : Type} [CommRing B] {J : Ideal B}

def fil (δ : DividedPowers J) (N : ℕ) : Ideal B :=
  Ideal.span {b | ∃ l : List (ℕ × B), (∀ p ∈ l, p.2 ∈ J) ∧ N ≤ (l.map Prod.fst).sum ∧
    b = (l.map fun p ↦ δ.dpow p.1 p.2).prod}

def IsLev (δ : DividedPowers J) (N : ℕ) : Prop := fil δ N = ⊥

structure IsPreDP (J : Ideal B) (γ : ℕ → B → B) : Prop where
  null : ∀ n x, x ∉ J → γ n x = 0
  zero : ∀ x ∈ J, γ 0 x = 1
  one : ∀ x ∈ J, γ 1 x = x
  mem : ∀ n, n ≠ 0 → ∀ x ∈ J, γ n x ∈ J
  add : ∀ n, ∀ x ∈ J, ∀ y ∈ J, γ n (x + y) = ∑ k ∈ Finset.HasAntidiagonal.antidiagonal n, γ k.1 x * γ k.2 y
  mul : ∀ n a, ∀ x ∈ J, γ n (a * x) = a ^ n * γ n x
  mul_dpow : ∀ m n, ∀ x ∈ J, γ m x * γ n x = ((m + n).choose m : B) * γ (m + n) x

structure PDPoly (B : Type) [CommRing B] : Type 1 where

  P : Type
  [ring : CommRing P]
  [alg : Algebra B P]

  e : Module.Basis ℕ B P
  e_zero : e 0 = 1
  e_mul : ∀ m n, e m * e n = ((m + n).choose m : P) * e (m + n)

attribute [instance] PDPoly.ring PDPoly.alg

def PDPoly.aug (Q : PDPoly B) : Ideal Q.P := Ideal.span (Set.range fun n : ℕ ↦ Q.e (n + 1))

def PDPoly.ext (Q : PDPoly B) (J : Ideal B) : Ideal Q.P := J.map (algebraMap B Q.P) ⊔ Q.aug

structure PDPoly.IsStd (Q : PDPoly B) (δ : DividedPowers J) (η : DividedPowers (Q.ext J)) : Prop where
  dp : IsDPMorphism δ η (algebraMap B Q.P)
  var : ∀ n, η.dpow n (Q.e 1) = Q.e n


set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
attribute [instance] _root_.GlobalTheory.PDA.PDPoly.ring
  _root_.GlobalTheory.PDA.PDPoly.alg in
theorem _root_.GlobalTheory.PDA.isLev_iff_prod (δ : DividedPowers J) (N : ℕ) :
    _root_.GlobalTheory.PDA.IsLev δ N ↔ ∀ l : List (ℕ × B), (∀ p ∈ l, p.2 ∈ J) →
      N ≤ (l.map Prod.fst).sum → (l.map fun p ↦ δ.dpow p.1 p.2).prod = 0 := by
  unfold _root_.GlobalTheory.PDA.IsLev _root_.GlobalTheory.PDA.fil
  rw [Ideal.span_eq_bot]
  constructor
  · intro h l hl hN
    exact h _ ⟨l, hl, hN, rfl⟩
  · rintro h _ ⟨l, hl, hN, rfl⟩
    exact h l hl hN


set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
attribute [instance] _root_.GlobalTheory.PDA.PDPoly.ring
  _root_.GlobalTheory.PDA.PDPoly.alg in
theorem _root_.GlobalTheory.PDA.isDPNilpotent_iff_exists_isLevel (δ : DividedPowers J) :
    _root_.GlobalTheory.Cris.IsNilDP δ ↔ ∃ N, _root_.GlobalTheory.PDA.IsLev δ N := by
  unfold _root_.GlobalTheory.Cris.IsNilDP
  exact exists_congr fun N => (_root_.GlobalTheory.PDA.isLev_iff_prod δ N).symm


set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
attribute [instance] _root_.GlobalTheory.PDA.PDPoly.ring
  _root_.GlobalTheory.PDA.PDPoly.alg in
theorem _root_.GlobalTheory.PDA.fil_zero_eq_top (δ : DividedPowers J) :
    _root_.GlobalTheory.PDA.fil δ 0 = ⊤ :=
  (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span ⟨[], by simp, by simp, by simp⟩)

set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
attribute [instance] _root_.GlobalTheory.PDA.PDPoly.ring
  _root_.GlobalTheory.PDA.PDPoly.alg in
private lemma prod_dpow_mem_of_one_le_sum (δ : DividedPowers J) :
    ∀ l : List (ℕ × B), (∀ p ∈ l, p.2 ∈ J) → 1 ≤ (l.map Prod.fst).sum →
      (l.map fun p ↦ δ.dpow p.1 p.2).prod ∈ J
  | [], _, h => by simp at h
  | p :: l, hl, h => by
    rw [List.map_cons, List.prod_cons]
    by_cases hp : p.1 = 0
    · refine J.mul_mem_left _ (prod_dpow_mem_of_one_le_sum δ l
        (fun q hq => hl q (List.mem_cons_of_mem _ hq)) ?_)
      simpa [hp] using h
    · exact J.mul_mem_right _ (δ.dpow_mem hp (hl p (by simp)))


set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
attribute [instance] _root_.GlobalTheory.PDA.PDPoly.ring
  _root_.GlobalTheory.PDA.PDPoly.alg in
theorem _root_.GlobalTheory.PDA.fil_one_eq (δ : DividedPowers J) :
    _root_.GlobalTheory.PDA.fil δ 1 = J := by
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨l, hl, hN, rfl⟩
    exact prod_dpow_mem_of_one_le_sum δ l hl hN
  · intro x hx
    exact Ideal.subset_span ⟨[(1, x)], by simpa using hx, by simp, by simp [δ.dpow_one hx]⟩


set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
attribute [instance] _root_.GlobalTheory.PDA.PDPoly.ring
  _root_.GlobalTheory.PDA.PDPoly.alg in
theorem _root_.GlobalTheory.PDA.PDPoly.e_succ_mem_aug (Q : _root_.GlobalTheory.PDA.PDPoly B)
    (n : ℕ) : Q.e (n + 1) ∈ Q.aug :=
  Ideal.subset_span ⟨n, rfl⟩


set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
attribute [instance] _root_.GlobalTheory.PDA.PDPoly.ring
  _root_.GlobalTheory.PDA.PDPoly.alg in
theorem _root_.GlobalTheory.PDA.PDPoly.e_one_mem_ext (Q : _root_.GlobalTheory.PDA.PDPoly B)
    (J : Ideal B) : Q.e 1 ∈ Q.ext J :=
  Ideal.mem_sup_right (Q.e_succ_mem_aug 0)


set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
attribute [instance] _root_.GlobalTheory.PDA.PDPoly.ring
  _root_.GlobalTheory.PDA.PDPoly.alg in
theorem _root_.GlobalTheory.PDA.PDPoly.algebraMap_mem_ext (Q : _root_.GlobalTheory.PDA.PDPoly B)
    {a : B} (ha : a ∈ J) :
    algebraMap B Q.P a ∈ Q.ext J :=
  Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)

section Inhabitants

open Polynomial TensorProduct

def ratBasis : Module.Basis ℕ ℚ ℚ[X] :=
  (basisMonomials ℚ).unitsSMul fun n ↦ Units.mk0 ((n.factorial : ℚ)⁻¹) (inv_ne_zero (by positivity))

set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
attribute [instance] _root_.GlobalTheory.PDA.PDPoly.ring
  _root_.GlobalTheory.PDA.PDPoly.alg in
open Polynomial TensorProduct in
private lemma ratBasis_eq_C_inv_factorial_mul_X_pow (n : ℕ) :
    _root_.GlobalTheory.PDA.ratBasis n = C ((n.factorial : ℚ)⁻¹) * X ^ n := by
  rw [_root_.GlobalTheory.PDA.ratBasis, Module.Basis.unitsSMul_apply, coe_basisMonomials, Units.smul_def,
    Units.val_mk0, smul_eq_C_mul, X_pow_eq_monomial]


set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
attribute [instance] _root_.GlobalTheory.PDA.PDPoly.ring
  _root_.GlobalTheory.PDA.PDPoly.alg in
open Polynomial TensorProduct in
theorem _root_.GlobalTheory.PDA.ratBasis_zero : _root_.GlobalTheory.PDA.ratBasis 0 = 1 := by
  rw [ratBasis_eq_C_inv_factorial_mul_X_pow]; simp


set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
attribute [instance] _root_.GlobalTheory.PDA.PDPoly.ring
  _root_.GlobalTheory.PDA.PDPoly.alg in
open Polynomial TensorProduct in
theorem _root_.GlobalTheory.PDA.ratBasis_mul (m n : ℕ) : _root_.GlobalTheory.PDA.ratBasis m * _root_.GlobalTheory.PDA.ratBasis n = ((m + n).choose m : ℚ[X]) * _root_.GlobalTheory.PDA.ratBasis (m + n) := by
  have key : ((m.factorial : ℚ)⁻¹ * (n.factorial : ℚ)⁻¹)
      = ((m + n).choose m : ℚ) * ((m + n).factorial : ℚ)⁻¹ := by
    have h := Nat.add_choose_mul_factorial_mul_factorial n m
    rw [add_comm n m] at h
    have hc : ((m + n).choose m : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    rw [← h]; push_cast; field_simp
  rw [ratBasis_eq_C_inv_factorial_mul_X_pow, ratBasis_eq_C_inv_factorial_mul_X_pow,
    ratBasis_eq_C_inv_factorial_mul_X_pow, ← map_natCast C, pow_add,
    show C ((m + n).choose m : ℚ) * (C ((m + n).factorial : ℚ)⁻¹ * (X ^ m * X ^ n))
      = C (((m + n).choose m : ℚ) * ((m + n).factorial : ℚ)⁻¹) * (X ^ m * X ^ n) by
        rw [C_mul]; ring, ← key, C_mul]
  ring


def intForm : Subalgebra ℤ ℚ[X] :=
  (Submodule.span ℤ (Set.range ratBasis)).toSubalgebra
    (ratBasis_zero ▸ Submodule.subset_span ⟨0, rfl⟩)
    (by
      intro x y hx hy
      refine Submodule.span_induction₂ (p := fun x y _ _ ↦ x * y ∈ Submodule.span ℤ (Set.range ratBasis))
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
      · rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
        rw [ratBasis_mul, ← nsmul_eq_mul]
        exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      · intro y _; simp
      · intro y _; simp
      · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
      · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
      · intro r x y _ _ h; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h
      · intro r x y _ _ h; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h)


set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
attribute [instance] _root_.GlobalTheory.PDA.PDPoly.ring
  _root_.GlobalTheory.PDA.PDPoly.alg in
open Polynomial TensorProduct in
theorem _root_.GlobalTheory.PDA.ratBasis_linearIndependent_int : LinearIndependent ℤ _root_.GlobalTheory.PDA.ratBasis :=
  _root_.GlobalTheory.PDA.ratBasis.linearIndependent.restrict_scalars' ℤ

def intBasis : Module.Basis ℕ ℤ intForm := Module.Basis.span ratBasis_linearIndependent_int

set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
attribute [instance] _root_.GlobalTheory.PDA.PDPoly.ring
  _root_.GlobalTheory.PDA.PDPoly.alg in
open Polynomial TensorProduct in
private lemma intBasis_cast_eq_ratBasis (n : ℕ) :
    (_root_.GlobalTheory.PDA.intBasis n : ℚ[X]) = _root_.GlobalTheory.PDA.ratBasis n := by
  exact congrArg Subtype.val
    (Module.Basis.span_apply _root_.GlobalTheory.PDA.ratBasis_linearIndependent_int n)


set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
attribute [instance] _root_.GlobalTheory.PDA.PDPoly.ring
  _root_.GlobalTheory.PDA.PDPoly.alg in
open Polynomial TensorProduct in
theorem _root_.GlobalTheory.PDA.intBasis_zero : _root_.GlobalTheory.PDA.intBasis 0 = 1 :=
  Subtype.ext (by simp [intBasis_cast_eq_ratBasis, _root_.GlobalTheory.PDA.ratBasis_zero])


set_option autoImplicit false in
open DividedPowers in
variable {B : Type} [CommRing B] {J : Ideal B} in
attribute [instance] _root_.GlobalTheory.PDA.PDPoly.ring
  _root_.GlobalTheory.PDA.PDPoly.alg in
open Polynomial TensorProduct in
theorem _root_.GlobalTheory.PDA.intBasis_mul (m n : ℕ) : _root_.GlobalTheory.PDA.intBasis m * _root_.GlobalTheory.PDA.intBasis n = ((m + n).choose m : _root_.GlobalTheory.PDA.intForm) * _root_.GlobalTheory.PDA.intBasis (m + n) :=
  Subtype.ext (by simp [intBasis_cast_eq_ratBasis, _root_.GlobalTheory.PDA.ratBasis_mul])

def stdPoly (B : Type) [CommRing B] : PDPoly B where
  P := B ⊗[ℤ] intForm
  e := Algebra.TensorProduct.basis B intBasis
  e_zero := by simp [intBasis_zero, Algebra.TensorProduct.one_def]
  e_mul m n := by
    simp only [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, intBasis_mul]
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, tmul_smul]

end Inhabitants

end GlobalTheory.PDA
