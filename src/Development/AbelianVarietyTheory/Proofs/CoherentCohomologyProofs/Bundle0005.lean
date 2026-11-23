module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MonomialMemReesAlgIff
section
open Polynomial

namespace GlobalTheory.ReesAlgebraMembership

variable {K A : Type*} [CommSemiring K] [Semiring A] [Algebra K A]

def reesAlg (M : ℕ → Submodule K A) [SetLike.GradedMonoid M] : Subalgebra K A[X] where
  carrier := {f | ∀ n, f.coeff n ∈ M n}
  add_mem' := fun {f g} hf hg n => by
    rw [coeff_add]
    exact (M n).add_mem (hf n) (hg n)
  mul_mem' := fun {f g} hf hg n => by
    rw [coeff_mul]
    refine (M n).sum_mem fun c hc => ?_
    have hn : c.1 + c.2 = n := by simpa using hc
    rw [← hn]
    exact SetLike.mul_mem_graded (hf c.1) (hg c.2)
  algebraMap_mem' := fun r n => by
    rw [Polynomial.algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h
      rw [Algebra.algebraMap_eq_smul_one]
      exact (M 0).smul_mem r (SetLike.one_mem_graded M)
    · exact (M n).zero_mem

variable (M : ℕ → Submodule K A) [SetLike.GradedMonoid M]

end GlobalTheory.ReesAlgebraMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
section
namespace GlobalTheory

open Finsupp

section Words

variable {R : Type*} [CommRing R] {Λ : Type*} {B : Type*} [Ring B] [Algebra R B]

def opWord (D : Λ → B) (w : List Λ) : B := (w.map D).prod

@[simp] theorem opWord_nil (D : Λ → B) : opWord D [] = 1 := rfl

@[simp] theorem opWord_cons (D : Λ → B) (l : Λ) (w : List Λ) :
    opWord D (l :: w) = D l * opWord D w := by simp [opWord]

theorem opWord_append (D : Λ → B) (w w' : List Λ) :
    opWord D (w ++ w') = opWord D w * opWord D w' := by simp [opWord]

theorem opWord_perm {D : Λ → B} (hD : ∀ l l', Commute (D l) (D l')) {w w' : List Λ}
    (h : w.Perm w') : opWord D w = opWord D w' := by
  induction h with
  | nil => rfl
  | cons l _ ih => simp [ih]
  | swap l l' w => simp only [opWord_cons, ← mul_assoc, (hD l l').eq]
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

def IsOrderingRule (ord : (Λ →₀ ℕ) → List Λ) : Prop :=
  ∀ α, (ord α : Multiset Λ) = Finsupp.toMultiset α

theorem isOrderingRule_toList :
    IsOrderingRule (fun α : Λ →₀ ℕ => (Finsupp.toMultiset α).toList) :=
  fun _ => Multiset.coe_toList _

noncomputable def opPoly (D : Λ → B) (ord : (Λ →₀ ℕ) → List Λ) : MvPolynomial Λ R →ₗ[R] B :=
  (MvPolynomial.basisMonomials Λ R).constr R (fun α => opWord D (ord α))

theorem opPoly_monomial (D : Λ → B) (ord : (Λ →₀ ℕ) → List Λ) (α : Λ →₀ ℕ) (c : R) :
    opPoly D ord (MvPolynomial.monomial α c) = c • opWord D (ord α) := by
  have h : MvPolynomial.monomial α c = c • MvPolynomial.basisMonomials Λ R α := by
    simp [MvPolynomial.smul_monomial]
  rw [h, map_smul, opPoly, Module.Basis.constr_basis]

theorem opPoly_mul_of_commute {D : Λ → B} (hD : ∀ l l', Commute (D l) (D l'))
    {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) (P Q : MvPolynomial Λ R) :
    opPoly D ord (P * Q) = opPoly D ord P * opPoly D ord Q := by
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [add_mul, map_add (f := _), hp, hq]
  | monomial α a =>
    induction Q using MvPolynomial.induction_on' with
    | add p q hp hq => simp only [mul_add, map_add (f := _), hp, hq]
    | monomial β b =>
      have hp : (ord (α + β)).Perm (ord α ++ ord β) := by
        rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, h, h, h, map_add (f := _)]
      rw [MvPolynomial.monomial_mul, opPoly_monomial, opPoly_monomial, opPoly_monomial,
        opWord_perm hD hp, opWord_append, smul_mul_smul_comm]

theorem IsOrderingRule.ord_zero {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) :
    ord 0 = [] := by
  have := h 0
  simpa using this

theorem IsOrderingRule.ord_single {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) (l : Λ) :
    ord (single l 1) = [l] := by
  have := h (single l 1)
  rw [Finsupp.toMultiset_single, one_smul] at this
  exact List.perm_singleton.mp (Multiset.coe_eq_coe.mp this)

theorem opPoly_C (D : Λ → B) {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) (c : R) :
    opPoly D ord (MvPolynomial.C c) = algebraMap R B c := by
  rw [MvPolynomial.C_apply, opPoly_monomial, h.ord_zero, opWord_nil, Algebra.algebraMap_eq_smul_one]

theorem opPoly_X (D : Λ → B) {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) (l : Λ) :
    opPoly D ord (MvPolynomial.X l : MvPolynomial Λ R) = D l := by
  rw [MvPolynomial.X, opPoly_monomial, h.ord_single]
  simp

noncomputable def commEval (D : Λ → B) (hD : ∀ l l', Commute (D l) (D l')) :
    MvPolynomial Λ R →ₐ[R] B :=
  AlgHom.ofLinearMap (opPoly D fun α => (Finsupp.toMultiset α).toList)
    (by rw [← MvPolynomial.C_1, opPoly_C D isOrderingRule_toList, map_one])
    (opPoly_mul_of_commute hD isOrderingRule_toList)

@[simp] theorem commEval_X (D : Λ → B) (hD : ∀ l l', Commute (D l) (D l')) (l : Λ) :
    commEval D hD (MvPolynomial.X l : MvPolynomial Λ R) = D l :=
  opPoly_X D isOrderingRule_toList l

end Words

section General

variable {R A M Λ : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M]

end General

section Constant

open MvPolynomial

variable {R σ Λ : Type*} [CommRing R]

def multiFactorial (α : σ →₀ ℕ) : ℕ := α.prod fun _ n => n.factorial

end Constant

section Series

open MvPowerSeries

variable {R σ Λ M : Type*} [CommRing R]

noncomputable abbrev germIdeal (σ R : Type*) [CommRing R] : Ideal (MvPowerSeries σ R) :=
  RingHom.ker (constantCoeff : MvPowerSeries σ R →+* R)

theorem X_mem_germIdeal (i : σ) : (X i : MvPowerSeries σ R) ∈ germIdeal σ R := by
  simp [RingHom.mem_ker]

theorem exists_eq_sum_X_mul [Fintype σ] {n : ℕ} {g : MvPowerSeries σ R}
    (hg : ∀ d : σ →₀ ℕ, degree d < n + 1 → coeff d g = 0) :
    ∃ h : σ → MvPowerSeries σ R, (∀ i (d : σ →₀ ℕ), degree d < n → coeff d (h i) = 0) ∧
      g = ∑ i, X i * h i := by
  classical
  have hidx : ∀ d : σ →₀ ℕ, d ≠ 0 → ∃ i, d i ≠ 0 := fun d hd => by
    by_contra hc
    push Not at hc
    exact hd (Finsupp.ext hc)
  choose idx hidx using hidx
  let part : σ → MvPowerSeries σ R := fun i d =>
    if hd : d ≠ 0 then (if idx d hd = i then coeff d g else 0) else 0
  have hpart : ∀ i d, coeff d (part i) =
      if hd : d ≠ 0 then (if idx d hd = i then coeff d g else 0) else 0 := fun _ _ => rfl
  have hdvd : ∀ i, (X i : MvPowerSeries σ R) ∣ part i := fun i => by
    rw [X_dvd_iff]
    intro d hd
    rw [hpart]
    split_ifs with h₁ h₂
    · exact absurd hd (h₂ ▸ hidx d h₁)
    · rfl
    · rfl
  choose h hh using hdvd
  refine ⟨h, fun i d hd => ?_, ?_⟩
  · have h₁ : coeff (single i 1 + d) (part i) = coeff d (h i) := by
      rw [hh, X_def, coeff_add_monomial_mul, one_mul]
    rw [← h₁, hpart]
    have h₂ : coeff (single i 1 + d) g = 0 := hg _ (by simp; omega)
    simp [h₂]
  · ext d
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← hh, map_sum, hpart]
    by_cases hd : d = 0
    · subst hd
      simpa using hg 0 (by simp)
    · simp [hd]

theorem germIdeal_eq_span [Finite σ] :
    germIdeal σ R = Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  cases nonempty_fintype σ
  refine le_antisymm (fun g hg => ?_) (Ideal.span_le.mpr ?_)
  · obtain ⟨h, -, rfl⟩ := exists_eq_sum_X_mul (n := 0) (g := g) fun d hd => by
      obtain rfl : d = 0 := by simpa [degree_eq_zero_iff] using hd
      simpa using hg
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    exact X_mem_germIdeal i

theorem mem_germIdeal_pow_iff [Finite σ] {n : ℕ} {g : MvPowerSeries σ R} :
    g ∈ germIdeal σ R ^ n ↔ ∀ d : σ →₀ ℕ, degree d < n → coeff d g = 0 := by
  cases nonempty_fintype σ
  constructor
  · intro hg
    suffices h : (n : ℕ∞) ≤ g.order from fun d hd =>
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
    induction n generalizing g with
    | zero => simp
    | succ n ih =>
      rw [pow_succ] at hg
      refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · refine le_trans ?_ le_order_mul
        push_cast
        refine add_le_add (ih ha) ?_
        exact_mod_cast nat_le_order (n := 1) fun d hd => by
          obtain rfl : d = 0 := by simpa [degree_eq_zero_iff] using hd
          simpa using hb
      · exact (le_min ha hb).trans min_order_le_add
  · induction n generalizing g with
    | zero => simp
    | succ n ih =>
      intro hg
      obtain ⟨h, hh, rfl⟩ := exists_eq_sum_X_mul hg
      rw [pow_succ']
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (X_mem_germIdeal i) (ih (hh i))

theorem mem_germIdeal_pow_iff_le_order [Finite σ] {n : ℕ} {g : MvPowerSeries σ R} :
    g ∈ germIdeal σ R ^ n ↔ (n : ℕ∞) ≤ g.order := by
  rw [mem_germIdeal_pow_iff]
  exact ⟨nat_le_order, fun h d hd => coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)⟩

variable [Finite σ]

end Series

section Symbol

open MvPowerSeries

variable {R σ Λ M : Type*} [CommRing R] [Finite σ] [AddCommGroup M] [Module R M]
  [Module (MvPowerSeries σ R) M]

variable [IsScalarTower R (MvPowerSeries σ R) M]

end Symbol

section Example

open MvPowerSeries

end Example

section Legendre

variable {l : ℕ} [hl : Fact l.Prime]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

end Legendre

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RootCharOfAddNatCast
section
namespace GlobalTheory.RootCharacter

open scoped BigOperators

variable {B : Type*} [CommMonoid B] {I : Type*} [Fintype I] {n : ℕ} [NeZero n]

theorem pow_val_add {x : B} (hx : x ^ n = 1) (a b : ZMod n) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hx]

def rootChar (u : I → B) (hu : ∀ q, u q ^ n = 1) : Multiplicative (I → ZMod n) →* B where
  toFun a := ∏ q, u q ^ (Multiplicative.toAdd a q).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun q _ => pow_val_add (hu q) _ _

end GlobalTheory.RootCharacter
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SigmaSplitSymmInl
section
namespace GlobalTheory.InnerAutomorphism

section Inner

variable {A : Type*} (R : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

def innerAut (u : Aˣ) : A ≃ₐ[R] A where
  toFun x := (u : A) * x * ((u⁻¹ : Aˣ) : A)
  invFun x := ((u⁻¹ : Aˣ) : A) * x * (u : A)
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_mul' x y := by simp [mul_assoc]
  map_add' x y := by simp [mul_add, add_mul]
  commutes' r := by rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

end Inner

section Bounded

variable {K n : Type*} [NormedField K]

def EntriesBounded (M : Matrix n n K) (c : ℝ) : Prop :=
  ∀ i j, ‖M i j‖ ≤ c

end Bounded

section DropLast

variable (K : Type*) [Semiring K] (d : ℕ)

def dropLast : (Fin (d + 1) → K) →ₗ[K] (Fin d → K) where
  toFun x i := x i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end DropLast

section Split

variable {ι : Type*} [DecidableEq ι] (F : ι → Type*)

def sigmaSplit (j : ι) : (Σ i, F i) ≃ F j ⊕ (Σ i : {i // i ≠ j}, F i.1) where
  toFun p := if h : p.1 = j then Sum.inl (h ▸ p.2) else Sum.inr ⟨⟨p.1, h⟩, p.2⟩
  invFun s := Sum.elim (fun x => ⟨j, x⟩) (fun q => ⟨q.1.1, q.2⟩) s
  left_inv := by
    rintro ⟨i, x⟩
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  right_inv := by
    rintro (x | ⟨⟨i, hi⟩, x⟩)
    · simp
    · simp [show ¬ i = j from hi]

theorem sigmaSplit_self (j : ι) (x : F j) : sigmaSplit F j ⟨j, x⟩ = Sum.inl x :=
  (Equiv.apply_eq_iff_eq_symm_apply _).2 rfl

theorem sigmaSplit_of_ne {i j : ι} (h : i ≠ j) (x : F i) :
    sigmaSplit F j ⟨i, x⟩ = Sum.inr ⟨⟨i, h⟩, x⟩ :=
  (Equiv.apply_eq_iff_eq_symm_apply _).2 rfl

end Split

end GlobalTheory.InnerAutomorphism
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed
section
open scoped PowerSeries TensorProduct

namespace GlobalTheory


open scoped PowerSeries TensorProduct in
theorem _root_.GlobalTheory.integralClosure_restrictScalars_of_isIntegral (A A' B : Type*) [CommRing A] [CommRing A']
    [CommRing B] [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
    [Algebra.IsIntegral A A'] :
    (integralClosure A' B).restrictScalars A = integralClosure A B := by
  ext x
  simp only [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  exact ⟨fun h => isIntegral_trans x h, fun h => h.tower_top⟩

section Contraction

variable {A : Type*} [CommRing A] (M : Submonoid A) {S : Type*} [CommRing S] [Algebra A S]
  [IsLocalization M S]

end Contraction

section PowerSeries

open PowerSeries IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

section Away

variable {ϖ : O} (hϖ : Irreducible ϖ) (S : Type*) [CommRing S] [Algebra O⟦X⟧ S]
  [IsLocalization.Away (C ϖ : O⟦X⟧) S]

include hϖ

variable (𝔭 : Ideal S) [𝔭.IsPrime] (h𝔭 : 𝔭 = Ideal.span {algebraMap O⟦X⟧ S X})
  (V : Type*) [CommRing V] [Algebra S V] [IsLocalization.AtPrime V 𝔭]

include h𝔭

end Away

end PowerSeries

universe u

end GlobalTheory
end

