module

public import Mathlib

@[expose] public section

namespace GlobalTheory

noncomputable section

open scoped NNReal TensorProduct

section CoeffSup

variable {ι M Γ₀ : Type*} [Zero M] [LinearOrderedCommMonoidWithZero Γ₀]

def coeffSup (N : M → Γ₀) (c : ι →₀ M) : Γ₀ := c.support.sup fun i => N (c i)

variable {N : M → Γ₀}

@[simp] theorem coeffSup_zero : coeffSup N (0 : ι →₀ M) = 0 := by
  simp [coeffSup, bot_eq_zero]

theorem coeffSup_le_iff (h0 : N 0 = 0) {c : ι →₀ M} {γ : Γ₀} :
    coeffSup N c ≤ γ ↔ ∀ i, N (c i) ≤ γ := by
  rw [coeffSup, Finset.sup_le_iff]
  refine ⟨fun h i => ?_, fun h i _ => h i⟩
  by_cases hi : i ∈ c.support
  · exact h i hi
  · rw [Finsupp.notMem_support_iff.mp hi, h0]; exact zero_le

theorem le_coeffSup (h0 : N 0 = 0) (c : ι →₀ M) (i : ι) : N (c i) ≤ coeffSup N c :=
  (coeffSup_le_iff h0).mp le_rfl i

theorem exists_mem_support_coeffSup_eq {c : ι →₀ M} (hc : c ≠ 0) :
    ∃ i ∈ c.support, coeffSup N c = N (c i) :=
  Finset.exists_mem_eq_sup _ (Finsupp.support_nonempty_iff.mpr hc) _

theorem coeffSup_eq_zero_iff (h0 : N 0 = 0) {c : ι →₀ M} :
    coeffSup N c = 0 ↔ ∀ i, N (c i) = 0 := by
  simp only [← le_zero_iff, coeffSup_le_iff h0]

theorem coeffSup_single (h0 : N 0 = 0) (i : ι) (a : M) :
    coeffSup N (Finsupp.single i a) = N a := by
  classical
  refine le_antisymm ((coeffSup_le_iff h0).mpr fun j => ?_) ?_
  · rw [Finsupp.single_apply]; split_ifs
    · exact le_rfl
    · rw [h0]; exact zero_le
  · simpa using le_coeffSup h0 (Finsupp.single i a) i

end CoeffSup

section MonoidAlgebra

variable {R G Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)

theorem coeffSup_coeff_mul_le [Add G] (f g : AddMonoidAlgebra R G) :
    coeffSup v (f * g).coeff ≤ coeffSup v f.coeff * coeffSup v g.coeff := by
  classical
  refine (coeffSup_le_iff v.map_zero).mpr fun m => ?_
  rw [AddMonoidAlgebra.coeff_mul]
  refine v.map_sum_le fun a _ => v.map_sum_le fun b _ => ?_
  dsimp only
  split_ifs
  · rw [v.map_mul]
    exact mul_le_mul' (le_coeffSup v.map_zero _ _) (le_coeffSup v.map_zero _ _)
  · rw [v.map_zero]; exact zero_le

theorem coeffSup_coeff_mul [Add G] [UniqueSums G] (f g : AddMonoidAlgebra R G) :
    coeffSup v (f * g).coeff = coeffSup v f.coeff * coeffSup v g.coeff := by
  classical
  refine le_antisymm (coeffSup_coeff_mul_le v f g) ?_
  by_cases hf : coeffSup v f.coeff = 0
  · simp [hf]
  by_cases hg : coeffSup v g.coeff = 0
  · simp [hg]
  have hf' : f.coeff ≠ 0 := fun h => hf (by simp [h])
  have hg' : g.coeff ≠ 0 := fun h => hg (by simp [h])
  obtain ⟨a, ha, ha'⟩ := exists_mem_support_coeffSup_eq (N := v) hf'
  obtain ⟨b, hb, hb'⟩ := exists_mem_support_coeffSup_eq (N := v) hg'
  obtain ⟨a₀, ha₀, b₀, hb₀, hu⟩ := UniqueSums.uniqueAdd_of_nonempty
    (A := f.coeff.support.filter fun x => v (f.coeff x) = coeffSup v f.coeff)
    (B := g.coeff.support.filter fun x => v (g.coeff x) = coeffSup v g.coeff)
    ⟨a, Finset.mem_filter.mpr ⟨ha, ha'.symm⟩⟩ ⟨b, Finset.mem_filter.mpr ⟨hb, hb'.symm⟩⟩
  obtain ⟨ha₁, ha₂⟩ := Finset.mem_filter.mp ha₀
  obtain ⟨hb₁, hb₂⟩ := Finset.mem_filter.mp hb₀
  refine le_trans (le_of_eq ?_) (le_coeffSup v.map_zero _ (a₀ + b₀))
  have hpos : 0 < coeffSup v f.coeff * coeffSup v g.coeff := zero_lt_iff.mpr (mul_ne_zero hf hg)
  rw [AddMonoidAlgebra.coeff_mul]
  simp_rw [Finsupp.sum]
  rw [← Finset.sum_product', v.map_sum_eq_of_lt (j := (a₀, b₀))
    (Finset.mem_product.mpr ⟨ha₁, hb₁⟩)]
  · simp [ha₂, hb₂]
  · intro p hp
    obtain ⟨hp, hne⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_singleton] at hne
    simp only [if_true, map_mul, ha₂, hb₂]
    split_ifs with he
    · rw [map_mul]
      have h₁ := le_coeffSup v.map_zero f.coeff p.1
      have h₂ := le_coeffSup v.map_zero g.coeff p.2
      rcases h₁.eq_or_lt with h₁ | h₁
      · rcases h₂.eq_or_lt with h₂ | h₂
        · have := hu (Finset.mem_filter.mpr ⟨hp₁, h₁⟩) (Finset.mem_filter.mpr ⟨hp₂, h₂⟩) he
          exact absurd (Prod.ext this.1 this.2) hne
        · rw [h₁]; exact mul_lt_mul_of_pos_left h₂ (zero_lt_iff.mpr hf)
      · exact lt_of_le_of_lt (mul_le_mul_right h₂ _)
          (mul_lt_mul_of_pos_right h₁ (zero_lt_iff.mpr hg))
    · rw [map_zero]; exact hpos

variable [AddMonoid G] [UniqueSums G]

def gaussValAlg : Valuation (AddMonoidAlgebra R G) Γ₀ where
  toFun f := coeffSup v f.coeff
  map_zero' := by simp
  map_one' := by
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, coeffSup_single v.map_zero,
      v.map_one]
  map_mul' := coeffSup_coeff_mul v
  map_add_le_max' f g := (coeffSup_le_iff v.map_zero).mpr fun m => by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact (v.map_add _ _).trans
      (max_le_max (le_coeffSup v.map_zero _ _) (le_coeffSup v.map_zero _ _))

theorem gaussValAlg_le_iff {f : AddMonoidAlgebra R G} {γ : Γ₀} :
    gaussValAlg v f ≤ γ ↔ ∀ m, v (f.coeff m) ≤ γ := coeffSup_le_iff v.map_zero

@[simp] theorem gaussValAlg_single (m : G) (a : R) :
    gaussValAlg v (AddMonoidAlgebra.single m a) = v a :=
  coeffSup_single v.map_zero m a

theorem gaussValAlg_eq_zero_iff {f : AddMonoidAlgebra R G} :
    gaussValAlg v f = 0 ↔ ∀ m, v (f.coeff m) = 0 := coeffSup_eq_zero_iff v.map_zero

end MonoidAlgebra

section Poly

open MvPolynomial

variable {R S Γ₀ σ τ : Type*} [CommRing R] [CommRing S] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀)

def gaussVal : Valuation (MvPolynomial σ R) Γ₀ := gaussValAlg v

theorem gaussVal_le_iff {f : MvPolynomial σ R} {γ : Γ₀} :
    gaussVal v f ≤ γ ↔ ∀ m, v (AddMonoidAlgebra.coeff f m) ≤ γ := gaussValAlg_le_iff v

theorem le_gaussVal (f : MvPolynomial σ R) (m : σ →₀ ℕ) : v (AddMonoidAlgebra.coeff f m) ≤ gaussVal v f :=
  (gaussVal_le_iff v).mp le_rfl m

theorem gaussVal_eq_zero_iff_forall {f : MvPolynomial σ R} :
    gaussVal v f = 0 ↔ ∀ m, v (AddMonoidAlgebra.coeff f m) = 0 := gaussValAlg_eq_zero_iff v

@[simp] theorem gaussVal_monomial (m : σ →₀ ℕ) (a : R) :
    gaussVal v (monomial m a) = v a := gaussValAlg_single v m a

@[simp] theorem gaussVal_C (a : R) : gaussVal v (C a : MvPolynomial σ R) = v a :=
  gaussVal_monomial v 0 a

@[simp] theorem gaussVal_X (i : σ) : gaussVal v (X i : MvPolynomial σ R) = 1 :=
  (gaussVal_monomial v _ 1).trans v.map_one

theorem gaussVal_supp :
    (gaussVal v).supp = v.supp.map (C : R →+* MvPolynomial σ R) := by
  ext f
  rw [Valuation.mem_supp_iff, gaussVal_eq_zero_iff_forall, mem_map_C_iff]
  simp only [Valuation.mem_supp_iff]

theorem gaussVal_supp_eq_bot_of_supp (hv : v.supp = ⊥) :
    (gaussVal (σ := σ) v).supp = ⊥ := by
  rw [gaussVal_supp, hv, Ideal.map_bot]

theorem gaussVal_sum_C_mul_X (s : Finset σ) (a : σ → R) :
    gaussVal v (∑ i ∈ s, C (a i) * X i : MvPolynomial σ R) = s.sup fun i => v (a i) := by
  classical
  refine le_antisymm (Valuation.map_sum_le _ fun i hi => ?_) (Finset.sup_le fun i hi => ?_)
  · rw [map_mul, gaussVal_C, gaussVal_X, mul_one]
    exact Finset.le_sup (f := fun i => v (a i)) hi
  · refine le_trans (le_of_eq ?_) (le_gaussVal v _ (Finsupp.single i 1))
    rw [coeff_sum, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [coeff_C_mul, coeff_X, if_neg, mul_zero]
      exact fun h => hj (Finsupp.single_left_injective one_ne_zero h)
    · exact fun h => absurd hi h

end Poly

section Field

open MvPolynomial

variable {K Γ₀ σ τ : Type*} [Field K]

section Monoid

variable [LinearOrderedCommMonoidWithZero Γ₀] [Nontrivial Γ₀] (v : Valuation K Γ₀)

end Monoid

variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

variable {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]

end Field

section Additive

open MvPolynomial

variable {R Γ σ τ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)

def gaussAddVal : AddValuation (MvPolynomial σ R) Γ :=
  AddValuation.ofValuation (gaussVal (AddValuation.toValuation v))

theorem gaussAddVal_mul (f g : MvPolynomial σ R) :
    gaussAddVal v (f * g) = gaussAddVal v f + gaussAddVal v g := AddValuation.map_mul _ f g

@[simp] theorem gaussAddVal_C (a : R) : gaussAddVal v (C a : MvPolynomial σ R) = v a :=
  gaussVal_C (AddValuation.toValuation v) a

@[simp] theorem gaussAddVal_X (i : σ) : gaussAddVal v (X i : MvPolynomial σ R) = 0 :=
  gaussVal_X (AddValuation.toValuation v) i

end Additive

section Abs

open MvPolynomial

variable {R σ τ : Type*} [CommRing R]

def absValuation [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a) :
    Valuation R ℝ≥0 where
  toFun x := NNReal.mk (a x) (a.nonneg x)
  map_zero' := NNReal.eq a.map_zero
  map_one' := NNReal.eq a.map_one
  map_mul' x y := NNReal.eq (a.map_mul x y)
  map_add_le_max' x y := by
    refine NNReal.coe_le_coe.mp ?_
    rw [NNReal.coe_max]
    exact ha x y

@[simp] theorem coe_absValuation [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a)
    (x : R) : (absValuation a ha x : ℝ) = a x := rfl

theorem absValuation_supp [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a) :
    (absValuation a ha).supp = ⊥ := by
  ext x
  rw [Valuation.mem_supp_iff, ← NNReal.coe_eq_zero, coe_absValuation, a.eq_zero, Ideal.mem_bot]

def valuationAbs (v : Valuation R ℝ≥0) (hv : v.supp = ⊥) : AbsoluteValue R ℝ where
  toFun x := v x
  map_mul' x y := by simp
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by
    rw [NNReal.coe_eq_zero, ← Valuation.mem_supp_iff, hv, Ideal.mem_bot]
  add_le' x y := by
    have h : (v (x + y) : ℝ) ≤ max (v x : ℝ) (v y) := by exact_mod_cast v.map_add x y
    exact h.trans (max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

variable [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a)

def gaussAbs : AbsoluteValue (MvPolynomial σ R) ℝ :=
  valuationAbs (gaussVal (absValuation a ha))
    (gaussVal_supp_eq_bot_of_supp _ (absValuation_supp a ha))

variable {K : Type*} [Field K] (a : AbsoluteValue K ℝ) (ha : IsNonarchimedean a)

variable {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]

end Abs

section Content

open MvPolynomial Module

variable {R Γ₀ ι κ σ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀) {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

def basisVal (b : Basis ι R M) (x : M) : Γ₀ := coeffSup v (b.repr x)

variable (b : Basis ι R M)

theorem basisVal_le_iff {x : M} {γ : Γ₀} : basisVal v b x ≤ γ ↔ ∀ i, v (b.repr x i) ≤ γ :=
  coeffSup_le_iff v.map_zero

end Content

section Lattice

open Module

variable {R Γ₀ ι κ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation R Γ₀) {M : Type*} [AddCommGroup M] [Module R M] (b : Basis ι R M)
  {O : Type*} [CommRing O] [Algebra O R] [Module O M] [IsScalarTower O R M]

end Lattice

section Tensor

open MvPolynomial Module

variable {O R S Γ₀ ι κ σ : Type*} [CommRing O] [CommRing R] [Algebra O R] [CommRing S]
  [Algebra O S] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
  {M : Type*} [AddCommGroup M] [Module O M] (b : Basis ι O M)

end Tensor

section AdditiveContent

open MvPolynomial Module

variable {R Γ ι κ σ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)

section

variable {M : Type*} [AddCommGroup M] [Module R M] (b : Basis ι R M)

def basisAddVal (x : M) : Γ :=
  OrderDual.ofDual (Multiplicative.toAdd (basisVal (AddValuation.toValuation v) b x))

theorem le_basisAddVal_iff {x : M} {γ : Γ} :
    γ ≤ basisAddVal v b x ↔ ∀ i, γ ≤ v (b.repr x i) :=
  basisVal_le_iff (AddValuation.toValuation v) b (γ := Multiplicative.ofAdd (OrderDual.toDual γ))

theorem basisAddVal_eq_inf_univ [Fintype ι] (x : M) :
    basisAddVal v b x = Finset.univ.inf fun i => v (b.repr x i) :=
  eq_of_forall_le_iff fun γ => by simp [le_basisAddVal_iff]

end

variable {O M : Type*} [CommRing O] [Algebra O R] [AddCommGroup M] [Module O M] (b : Basis ι O M)

end AdditiveContent

section More

open MvPolynomial Module IsDedekindDomain

end More

section Examples

open MvPolynomial

end Examples

end

end GlobalTheory
