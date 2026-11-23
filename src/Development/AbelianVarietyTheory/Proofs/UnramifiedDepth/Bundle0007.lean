module

public import Mathlib
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
public import ReciprocityTheory.DualLattices.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightSubstNonneg
section
open ReciprocityTheory.PGsh

namespace GlobalTheory.WeightSubst

open MvPowerSeries

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type} [Fintype σ]
  [DecidableEq σ] (ρ : σ → ℝ)

def WtNonneg (g : MvPowerSeries σ C) : Prop :=
  ∀ α : σ →₀ ℕ, ((0 - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (coeff α g)

omit [Fintype σ] in
theorem wtNonneg_one : WtNonneg v ρ (1 : MvPowerSeries σ C) := by
  intro α
  rw [coeff_one]
  split_ifs with h
  · subst h
    simp
  · simp

omit [Fintype σ] in
theorem wtNonneg_mul {f g : MvPowerSeries σ C} (hf : WtNonneg v ρ f) (hg : WtNonneg v ρ g) :
    WtNonneg v ρ (f * g) := by
  intro α
  rw [coeff_mul]
  apply AddValuation.map_le_sum
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [AddValuation.map_mul]
  have e : ((0 - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) =
      ((0 - p.1.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) +
        ((0 - p.2.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_add, ← hp, Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring)]
    congr 1
    ring
  rw [e]
  exact add_le_add (hf p.1) (hg p.2)

omit [Fintype σ] in
theorem wtNonneg_prod {ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries σ C)
    (h : ∀ i ∈ s, WtNonneg v ρ (f i)) : WtNonneg v ρ (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using wtNonneg_one v ρ
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact wtNonneg_mul v ρ (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

omit [Fintype σ] in
theorem wtNonneg_pow {f : MvPowerSeries σ C} (hf : WtNonneg v ρ f) (n : ℕ) :
    WtNonneg v ρ (f ^ n) := by
  induction n with
  | zero => simpa using wtNonneg_one v ρ
  | succ k ih =>
    rw [pow_succ]
    exact wtNonneg_mul v ρ ih hf

theorem weight_subst_nonneg :
  (∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (σ τ : Type) [Fintype σ] [DecidableEq σ] [Fintype τ] (ρ : σ → ℝ) (K : MvPowerSeries τ C) (t : τ → MvPowerSeries σ C),
    MvIsInt v K → (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ c, (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (t c)))) → (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (MvPowerSeries.subst t K)))) := by
  intro C _ v σ τ _ _ _ ρ K t hK ht0 ht α
  have hs : MvPowerSeries.HasSubst t := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  rw [MvPowerSeries.coeff_subst hs, finsum_eq_sum _ (MvPowerSeries.coeff_subst_finite hs K α)]
  apply AddValuation.map_le_sum
  intro d _
  rw [smul_eq_mul, AddValuation.map_mul]
  have h1 : (0 : WithTop ℝ) ≤ v (MvPowerSeries.coeff d K) := hK d
  have h2 : WtNonneg v ρ (d.prod fun c e => t c ^ e) := by
    unfold Finsupp.prod
    exact wtNonneg_prod v ρ _ _ (fun c _ => wtNonneg_pow v ρ (ht c) _)
  have h3 := add_le_add h1 (h2 α)
  rwa [zero_add] at h3

end GlobalTheory.WeightSubst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightedOrderGePrimePowOfSumPurePowersAdd
section
open ReciprocityTheory.PGsh

namespace GlobalTheory.WeightFrobenius

open MvPowerSeries

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {M : ℕ} (ρ : Fin M → ℝ)

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
private theorem ordGe_iff_forall_le_valuation_coeff {f : MvPowerSeries (Fin M) C} {w : ℝ} :
    _root_.ReciprocityTheory.PGsh.OrdGe v ρ f w ↔
      ∀ α : Fin M →₀ ℕ, ((w - ∑ m, ρ m * (α m : ℝ) : ℝ) : WithTop ℝ) ≤ v (coeff α f) := by
  unfold _root_.ReciprocityTheory.PGsh.OrdGe
  exact Iff.rfl

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
private theorem ordGe_add' {f g : MvPowerSeries (Fin M) C} {w : ℝ}
    (hf : _root_.ReciprocityTheory.PGsh.OrdGe v ρ f w) (hg : _root_.ReciprocityTheory.PGsh.OrdGe v ρ g w) : _root_.ReciprocityTheory.PGsh.OrdGe v ρ (f + g) w := by
  rw [ordGe_iff_forall_le_valuation_coeff] at *
  intro α
  rw [map_add (f := _)]
  exact le_trans (le_min (hf α) (hg α)) (v.map_add _ _)

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
private theorem ordGe_zero_left {w : ℝ} : _root_.ReciprocityTheory.PGsh.OrdGe v ρ (0 : MvPowerSeries (Fin M) C) w := by
  rw [ordGe_iff_forall_le_valuation_coeff]
  intro α
  simp

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
private theorem ordGe_finset_sum {ι : Type} (s : Finset ι) {f : ι → MvPowerSeries (Fin M) C}
    {w : ℝ} (hf : ∀ i ∈ s, _root_.ReciprocityTheory.PGsh.OrdGe v ρ (f i) w) : _root_.ReciprocityTheory.PGsh.OrdGe v ρ (∑ i ∈ s, f i) w :=
  Finset.sum_induction f (fun g => _root_.ReciprocityTheory.PGsh.OrdGe v ρ g w) (fun _ _ => ordGe_add')
    ordGe_zero_left hf

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
private theorem ordGe_mul_natCast_of_le_valuation {f : MvPowerSeries (Fin M) C} {w t : ℝ} {c : ℕ}
    (hf : _root_.ReciprocityTheory.PGsh.OrdGe v ρ f w) (hc : (t : WithTop ℝ) ≤ v (c : C)) :
    _root_.ReciprocityTheory.PGsh.OrdGe v ρ (f * (c : MvPowerSeries (Fin M) C)) (w + t) := by
  rw [ordGe_iff_forall_le_valuation_coeff] at *
  intro α
  rw [← map_natCast (MvPowerSeries.C : C →+* MvPowerSeries (Fin M) C) c, coeff_mul_C,
    AddValuation.map_mul]
  have h : ((w + t - ∑ m, ρ m * (α m : ℝ) : ℝ) : WithTop ℝ) =
      ((w - ∑ m, ρ m * (α m : ℝ) : ℝ) : WithTop ℝ) + (t : WithTop ℝ) := by
    rw [← WithTop.coe_add]
    congr 1
    ring
  rw [h]
  exact add_le_add (hf α) hc

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
private theorem ordGe_mul' {f g : MvPowerSeries (Fin M) C} {a b : ℝ}
    (hf : _root_.ReciprocityTheory.PGsh.OrdGe v ρ f a) (hg : _root_.ReciprocityTheory.PGsh.OrdGe v ρ g b) : _root_.ReciprocityTheory.PGsh.OrdGe v ρ (f * g) (a + b) := by
  rw [ordGe_iff_forall_le_valuation_coeff] at *
  intro α
  rw [coeff_mul]
  refine AddValuation.map_le_sum v fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  subst hp
  rw [AddValuation.map_mul]
  have h : ((a + b - ∑ m, ρ m * ((p.1 + p.2) m : ℝ) : ℝ) : WithTop ℝ) =
      ((a - ∑ m, ρ m * (p.1 m : ℝ) : ℝ) : WithTop ℝ) +
        ((b - ∑ m, ρ m * (p.2 m : ℝ) : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_add]
    congr 1
    simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
    ring
  rw [h]
  exact add_le_add (hf _) (hg _)

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
private theorem ordGe_one_zero : _root_.ReciprocityTheory.PGsh.OrdGe v ρ (1 : MvPowerSeries (Fin M) C) 0 := by
  rw [ordGe_iff_forall_le_valuation_coeff]
  intro α
  rw [coeff_one]
  split_ifs with h
  · subst h
    simp
  · simp

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
private theorem ordGe_pow_unramified_depth {f : MvPowerSeries (Fin M) C} {a : ℝ}
    (hf : _root_.ReciprocityTheory.PGsh.OrdGe v ρ f a) (n : ℕ) : _root_.ReciprocityTheory.PGsh.OrdGe v ρ (f ^ n) (n * a) := by
  induction n with
  | zero => simpa using (ordGe_one_zero : _root_.ReciprocityTheory.PGsh.OrdGe v ρ (1 : MvPowerSeries (Fin M) C) 0)
  | succ n ih =>
    rw [pow_succ, show ((n + 1 : ℕ) : ℝ) * a = n * a + a by push_cast; ring]
    exact ordGe_mul' ih hf

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
private theorem one_le_valuation_natCast_of_dvd_of_valuation_eq_one {l c : ℕ} (hv : v (l : C) = 1) (h : l ∣ c) :
    ((1 : ℝ) : WithTop ℝ) ≤ v (c : C) := by
  obtain ⟨m, rfl⟩ := h
  have hm := _root_.ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.intCast_nonneg v (m : ℤ)
  rw [Int.cast_natCast] at hm
  rw [Nat.cast_mul, AddValuation.map_mul, hv]
  simpa [add_comm] using add_le_add_left hm (1 : WithTop ℝ)

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
private theorem ordGe_mono' {f : MvPowerSeries (Fin M) C} {w w' : ℝ}
    (hf : _root_.ReciprocityTheory.PGsh.OrdGe v ρ f w) (hw : w' ≤ w) : _root_.ReciprocityTheory.PGsh.OrdGe v ρ f w' := by
  rw [ordGe_iff_forall_le_valuation_coeff] at *
  intro α
  exact le_trans (WithTop.coe_le_coe.2 (by linarith)) (hf α)

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
private theorem ordGe_add_pow_sub_pow_sub_pow_of_valuation_eq_one {l k : ℕ} (hl : l.Prime)
    (hv : v (l : C) = 1) {f g : MvPowerSeries (Fin M) C} {w : ℝ}
    (hf : _root_.ReciprocityTheory.PGsh.OrdGe v ρ f w) (hg : _root_.ReciprocityTheory.PGsh.OrdGe v ρ g w) :
    _root_.ReciprocityTheory.PGsh.OrdGe v ρ ((f + g) ^ (l ^ k) - f ^ (l ^ k) - g ^ (l ^ k)) (1 + (l : ℝ) ^ k * w) := by
  obtain ⟨n, hn⟩ : ∃ n, l ^ k = n + 1 := ⟨l ^ k - 1, (Nat.succ_pred_eq_of_pos (pow_pos hl.pos k)).symm⟩
  have hlk : (l : ℝ) ^ k = n + 1 := by exact_mod_cast hn
  rw [hlk, hn]
  have key : (f + g) ^ (n + 1) - f ^ (n + 1) - g ^ (n + 1) = ∑ i ∈ Finset.range n,
      f ^ (i + 1) * g ^ (n + 1 - (i + 1)) * ((n + 1).choose (i + 1) : MvPowerSeries (Fin M) C) := by
    rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.choose_self, Nat.choose_zero_right, Nat.sub_self, Nat.sub_zero, pow_zero,
      Nat.cast_one, mul_one, one_mul]
    abel
  rw [key]
  refine ordGe_finset_sum _ fun i hi => ?_
  have hi' : i < n := Finset.mem_range.1 hi
  have hdvd : l ∣ (n + 1).choose (i + 1) := by
    rw [← hn]
    exact hl.dvd_choose_pow (Nat.succ_ne_zero i) (by omega)
  have h := ordGe_mul_natCast_of_le_valuation
    (ordGe_mul' (ordGe_pow_unramified_depth hf (i + 1)) (ordGe_pow_unramified_depth hg (n + 1 - (i + 1))))
    (one_le_valuation_natCast_of_dvd_of_valuation_eq_one hv hdvd)
  refine ordGe_mono' h (le_of_eq ?_)
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
private theorem ordGe_sum_pow_sub_sum_pow_of_valuation_eq_one {l k : ℕ} (hl : l.Prime)
    (hv : v (l : C) = 1) {ι : Type} (s : Finset ι) {x : ι → MvPowerSeries (Fin M) C} {w : ℝ}
    (hx : ∀ i ∈ s, _root_.ReciprocityTheory.PGsh.OrdGe v ρ (x i) w) :
    _root_.ReciprocityTheory.PGsh.OrdGe v ρ ((∑ i ∈ s, x i) ^ (l ^ k) - ∑ i ∈ s, x i ^ (l ^ k)) (1 + (l : ℝ) ^ k * w) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero k hl.ne_zero), sub_zero]
    exact ordGe_zero_left
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hxa := hx a (Finset.mem_insert_self a s)
    have hxs : ∀ i ∈ s, _root_.ReciprocityTheory.PGsh.OrdGe v ρ (x i) w := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have h := ordGe_add' (ordGe_add_pow_sub_pow_sub_pow_of_valuation_eq_one (k := k) hl hv hxa
      (ordGe_finset_sum s hxs)) (ih hxs)
    convert h using 1
    ring

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
private theorem ordGe_sum_add_pow_sub_sum_pow_ge_min {l k : ℕ} (hl : l.Prime) (hv : v (l : C) = 1)
    {x : Fin M → MvPowerSeries (Fin M) C} {ν : MvPowerSeries (Fin M) C} {w w₂ : ℝ}
    (hw : w ≤ w₂) (hx : ∀ j, _root_.ReciprocityTheory.PGsh.OrdGe v ρ (x j) w) (hν : _root_.ReciprocityTheory.PGsh.OrdGe v ρ ν w₂) :
    _root_.ReciprocityTheory.PGsh.OrdGe v ρ ((∑ j, x j + ν) ^ (l ^ k) - ∑ j, x j ^ (l ^ k))
      (min (1 + (l : ℝ) ^ k * w) ((l : ℝ) ^ k * w₂)) := by
  have hS := ordGe_finset_sum Finset.univ fun j _ => hx j
  have h₁ := ordGe_add_pow_sub_pow_sub_pow_of_valuation_eq_one (k := k) hl hv hS
    (ordGe_mono' hν hw)
  have h₂ := ordGe_pow_unramified_depth hν (l ^ k)
  have h₃ := ordGe_sum_pow_sub_sum_pow_of_valuation_eq_one (k := k) hl hv Finset.univ fun j _ => hx j
  push_cast at h₂
  have h := ordGe_add' (ordGe_add' (ordGe_mono' h₁ (min_le_left _ _))
    (ordGe_mono' h₂ (min_le_right _ _))) (ordGe_mono' h₃ (min_le_left _ _))
  convert h using 1
  ring

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
private theorem ordGe_C_mul_X_pow_of_le_valuation {r w : ℝ} {a : C} (j : Fin M) (N : ℕ)
    (ha : ((w - r * N : ℝ) : WithTop ℝ) ≤ v a) :
    _root_.ReciprocityTheory.PGsh.OrdGe v (fun _ => r)
      (MvPowerSeries.C (R := C) a * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ N) w := by
  rw [ordGe_iff_forall_le_valuation_coeff]
  intro α
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · subst h
    simpa [Finsupp.single_apply] using ha
  · simp

open MvPowerSeries in
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {M : ℕ} (ρ : Fin M → ℝ) in
theorem _root_.GlobalTheory.WeightFrobenius.main :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (M N k : ℕ) (r w w₂ : ℝ) (a : Fin M → C) (ν : MvPowerSeries (Fin M) C), w ≤ w₂ → (∀ j, ((w - r * N : ℝ) : WithTop ℝ) ≤ v (a j)) →
    _root_.ReciprocityTheory.PGsh.OrdGe v (fun _ => r) ν w₂ → _root_.ReciprocityTheory.PGsh.OrdGe v (fun _ => r) ((∑ j, MvPowerSeries.C (R := C) (a j) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ N + ν) ^ (l ^ k) -
      ∑ j, MvPowerSeries.C (R := C) (a j ^ (l ^ k)) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ (N * l ^ k)) (min (1 + (l : ℝ) ^ k * w) ((l : ℝ) ^ k * w₂))) := by
  intro C _ _ v l hl hv M N k r w w₂ a ν hw ha hν
  rw [show (∑ j, MvPowerSeries.C (R := C) (a j ^ (l ^ k)) *
      (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ (N * l ^ k)) =
      ∑ j, (MvPowerSeries.C (R := C) (a j) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ N) ^ (l ^ k)
    from Finset.sum_congr rfl fun j _ => by rw [mul_pow, ← map_pow, ← pow_mul]]
  exact ordGe_sum_add_pow_sub_sum_pow_ge_min hl hv hw (fun j => ordGe_C_mul_X_pow_of_le_valuation j N (ha j)) hν

end GlobalTheory.WeightFrobenius
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WtAddSingle
section
open ReciprocityTheory.PGsh

noncomputable section

namespace GlobalTheory.DetPowPairing

open MvPolynomial

variable {σ : Type} {C : Type} [CommRing C]

def wt (C : Type) [CommRing C] (A : σ →₀ ℕ) : C := A.prod fun _ e => (e.factorial : C)

def pair : MvPolynomial σ C →ₗ[C] MvPolynomial σ C →ₗ[C] C :=
  (basisMonomials σ C).constr C fun A => wt C A • lcoeff C A

theorem pair_monomial (A : σ →₀ ℕ) (c : C) (Q : MvPolynomial σ C) :
    pair (monomial A c) Q = c * wt C A * AddMonoidAlgebra.coeff Q A := by
  have h : monomial A c = c • (basisMonomials σ C) A := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, pair, Module.Basis.constr_basis, LinearMap.smul_apply, LinearMap.smul_apply, lcoeff_apply,
    smul_eq_mul, smul_eq_mul, mul_assoc]

theorem pair_eq (P Q : MvPolynomial σ C) :
    pair P Q = ∑ A ∈ P.support, AddMonoidAlgebra.coeff P A * wt C A * AddMonoidAlgebra.coeff Q A := by
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun A _ => pair_monomial A (AddMonoidAlgebra.coeff P A) Q

theorem wt_add_single (A : σ →₀ ℕ) (j : σ) :
    wt C (A + Finsupp.single j 1) = wt C A * ((A j : C) + 1) := by
  classical
  set s := A.support ∪ {j} with hs
  have hA : wt C A = ∏ i ∈ s, ((A i).factorial : C) :=
    Finsupp.prod_of_support_subset A Finset.subset_union_left _ (fun _ _ => by simp)
  have hsupp : (A + Finsupp.single j 1).support ⊆ s := by
    intro i hi
    rw [Finsupp.mem_support_iff] at hi
    by_cases h : i = j
    · simp [s, h]
    · have hAi : A i ≠ 0 := by simpa [Finsupp.single_apply, Ne.symm h] using hi
      simp [s, Finsupp.mem_support_iff, hAi]
  have hB : wt C (A + Finsupp.single j 1) = ∏ i ∈ s, (((A + Finsupp.single j 1 : σ →₀ ℕ) i).factorial : C) :=
    Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => by simp)
  have hj : j ∈ s := by simp [s]
  have hrest : ∏ i ∈ s.erase j, (((A + Finsupp.single j 1 : σ →₀ ℕ) i).factorial : C) =
      ∏ i ∈ s.erase j, ((A i).factorial : C) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp [Ne.symm hij]
  rw [hA, hB, ← Finset.mul_prod_erase s _ hj, ← Finset.mul_prod_erase s _ hj, hrest]
  simp [Nat.factorial_succ]
  ring

theorem coeff_pderiv' (j : σ) (A : σ →₀ ℕ) (Q : MvPolynomial σ C) :
    AddMonoidAlgebra.coeff (pderiv j Q) A = AddMonoidAlgebra.coeff Q (A + Finsupp.single j 1) * ((A j : C) + 1) :=
  coeff_pderiv Q A

theorem pair_X_mul (j : σ) (P Q : MvPolynomial σ C) :
    pair (P * X j) Q = pair P (pderiv j Q) := by
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pair_eq P, Finset.sum_mul, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [show (X j : MvPolynomial σ C) = monomial (Finsupp.single j 1) 1 from rfl, monomial_mul, mul_one,
    pair_monomial, coeff_pderiv', wt_add_single]
  ring

theorem pair_list {ι : Type} (f : ι → σ) (l : List ι) (P Q : MvPolynomial σ C) :
    pair (P * (l.map fun j => X (f j)).prod) Q =
      pair P (((l.map fun j => ((pderiv (f j) : Derivation C _ _) :
        MvPolynomial σ C →ₗ[C] MvPolynomial σ C)).prod : Module.End C (MvPolynomial σ C)) Q) := by
  induction l generalizing P with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← mul_assoc, ih, pair_X_mul]
    rfl

theorem pair_det (n : ℕ) (P Q : MvPolynomial (Fin n × Fin n) C) :
    pair (P * cayDet n C) Q = pair P (cayOp n C Q) := by
  have hdet : cayDet n C = ∑ s : Equiv.Perm (Fin n),
      (Equiv.Perm.sign s : ℤ) • ((List.finRange n).map fun i => (X (s i, i) : MvPolynomial _ C)).prod := by
    rw [cayDet, Matrix.det_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Units.smul_def, Fin.prod_univ_def]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hdet, cayOp, Finset.mul_sum, map_sum, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_smul_comm, map_zsmul, LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul]
  exact congrArg (fun t => (Equiv.Perm.sign s : ℤ) • t) (pair_list (fun i => (s i, i)) (List.finRange n) P Q)

theorem pair_pow (n x : ℕ) :
    (∏ c ∈ Finset.range n, (c.factorial : C)) * pair (cayDet n C ^ x) (cayDet n C ^ x) =
      ∏ c ∈ Finset.range n, ((x + c).factorial : C) := by
  induction x with
  | zero =>
    have h1 : pair (1 : MvPolynomial (Fin n × Fin n) C) 1 = 1 := by
      rw [show (1 : MvPolynomial (Fin n × Fin n) C) = monomial 0 1 from rfl, pair_monomial]
      simp [wt]
    simp [h1]
  | succ x ih =>
    have hc := cayley n C (x + 1)
    rw [Nat.add_sub_cancel] at hc
    have hp : pair (cayDet n C ^ (x + 1)) (cayDet n C ^ (x + 1)) =
        pair (cayDet n C ^ x) (cayOp n C (cayDet n C ^ (x + 1))) := by
      rw [← pair_det, ← pow_succ]
    rw [hp, hc, map_nsmul, nsmul_eq_mul, Nat.cast_prod, mul_left_comm, ih,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [show x + 1 + c = (x + c) + 1 by ring, Nat.factorial_succ]
    push_cast
    ring

theorem main :
    (∀ (C : Type) [Field C] [CharZero C] (n₀ x : ℕ), (∏ c ∈ Finset.range n₀, (c.factorial : C)) * (∑ A ∈ (cayDet n₀ C ^ x).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ x) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (cayDet n₀ C ^ x) A) = ∏ c ∈ Finset.range n₀, ((x + c).factorial : C)) := by
  intro C _ _ n₀ x
  have h := pair_pow (C := C) n₀ x
  rw [pair_eq] at h
  exact h

end GlobalTheory.DetPowPairing
end
end

