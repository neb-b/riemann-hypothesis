module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdEApply
section
noncomputable section

namespace GlobalTheory.StableLatCount

def adE (E : Type) [Field E] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂]
    (g₁ : A₁) (g₂ : A₂) : (A₂ →ₗ[E] A₁) →ₗ[E] (A₂ →ₗ[E] A₁) :=
  LinearMap.llcomp E A₂ A₁ A₁ (LinearMap.mulLeft E g₁) - LinearMap.lcomp E A₁ (LinearMap.mulLeft E g₂)

def homLat (E : Type) [Field E] {O A₁ A₂ : Type} [CommRing O] [Algebra O E] [CommRing A₁] [CommRing A₂]
    [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁]
    (M₁ : Submodule O A₁) (M₂ : Submodule O A₂) : Submodule O (A₂ →ₗ[E] A₁) where
  carrier := {ψ | ∀ x ∈ M₂, ψ x ∈ M₁}
  add_mem' := fun ha hb x hx => by simpa using M₁.add_mem (ha x hx) (hb x hx)
  zero_mem' := fun x _ => by simp
  smul_mem' := fun c ψ hψ x hx => by simpa using M₁.smul_mem c (hψ x hx)

theorem adE_apply (E : Type) [Field E] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂]
    (g₁ : A₁) (g₂ : A₂) (ψ : A₂ →ₗ[E] A₁) (x : A₂) : adE E g₁ g₂ ψ x = g₁ * ψ x - ψ (g₂ * x) := rfl

end GlobalTheory.StableLatCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemIntegralSolutionCountOfOrderOne
section
noncomputable section

namespace GlobalTheory.PMonE.LinCount

open Finset GlobalTheory.PMonE

variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]

def lin (K : ℕ) (M : ℕ → Matrix m m F) (k : ℕ) : Matrix (Fin (K + 1) × m) (Fin (K + 1) × m) F :=
  fun r c =>
    if r.1 = Fin.last K then
      (if k = 0 then M c.1 r.2 c.2 else if c.1 = Fin.last K then M (k + K) r.2 c.2 else 0)
    else
      (if k = 0 then (if (c.1 : ℕ) = r.1 + 1 ∧ r.2 = c.2 then -1 else 0)
        else if k = 1 then (if r = c then 1 else 0) else 0)

theorem lin_normal (K : ℕ) (M : ℕ → Matrix m m F) (h : Normal (K + 1) M) : Normal 1 (lin K M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n r c
    unfold lin
    split_ifs <;> first | exact h.int _ _ _ | simp
  · ext ⟨i, a⟩ ⟨j, b⟩
    have h1 : M (1 + K) = 1 := by rw [add_comm]; exact h.top
    by_cases hi : i = Fin.last K
    · subst hi
      by_cases hj : j = Fin.last K
      · subst hj
        simp [lin, h1, Matrix.one_apply]
      · simp [lin, hj, Matrix.one_apply, Ne.symm hj]
    · simp [lin, hi, Matrix.one_apply]
  · intro n hn r c
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    simp only [lin, h0, h1, if_false]
    split_ifs
    · exact h.small _ (by omega) _ _
    · simp
    · simp

theorem lin_zero_cast (K : ℕ) (M : ℕ → Matrix m m F) (Y : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    (lin K M 0).mulVec Y (i.castSucc, a) = - Y (i.succ, a) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (i.succ, a)]
  · simp [lin, (Fin.castSucc_lt_last i).ne]
  · rintro ⟨j, b⟩ _ hne
    have : ¬ ((j : ℕ) = i + 1 ∧ a = b) := by
      rintro ⟨h1, rfl⟩
      exact hne (by congr 1; exact Fin.ext (by simpa using h1))
    simp [lin, (Fin.castSucc_lt_last i).ne, this]
  · simp

theorem lin_one_cast (K : ℕ) (M : ℕ → Matrix m m F) (Y : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    (lin K M 1).mulVec Y (i.castSucc, a) = Y (i.castSucc, a) := by
  simp [Matrix.mulVec, dotProduct, lin, (Fin.castSucc_lt_last i).ne]

theorem lin_two_cast (K : ℕ) (M : ℕ → Matrix m m F) (k : ℕ) (Y : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    (lin K M (k + 1 + 1)).mulVec Y (i.castSucc, a) = 0 := by
  simp [Matrix.mulVec, dotProduct, lin, (Fin.castSucc_lt_last i).ne]

theorem lin_zero_last (K : ℕ) (M : ℕ → Matrix m m F) (Y : Fin (K + 1) × m → F) (a : m) :
    (lin K M 0).mulVec Y (Fin.last K, a) = ∑ j : Fin (K + 1), (M j).mulVec (fun b => Y (j, b)) a := by
  simp [Matrix.mulVec, dotProduct, lin, Fintype.sum_prod_type]

theorem lin_succ_last (K : ℕ) (M : ℕ → Matrix m m F) (k : ℕ) (Y : Fin (K + 1) × m → F) (a : m) :
    (lin K M (k + 1)).mulVec Y (Fin.last K, a) = (M (k + 1 + K)).mulVec (fun b => Y (Fin.last K, b)) a := by
  simp only [Matrix.mulVec, dotProduct, lin, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (Fin.last K)]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem lin_det (K : ℕ) (M : ℕ → Matrix m m F) (h : (M 0).det ≠ 0) : (lin K M 0).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hs : ∀ (i : Fin K) (a : m), v (i.succ, a) = 0 := by
    intro i a
    have := congrFun hv0 (i.castSucc, a)
    rw [lin_zero_cast] at this
    simpa using this
  have hz : (M 0).mulVec (fun b => v (0, b)) = 0 := by
    funext a
    have := congrFun hv0 (Fin.last K, a)
    rw [lin_zero_last, Fin.sum_univ_succ] at this
    simpa [hs, Matrix.mulVec, dotProduct] using this
  have h00 : (fun b => v (0, b)) = 0 := by
    by_contra hne
    exact h (Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hne, hz⟩)
  apply hv
  funext ⟨j, b⟩
  refine Fin.cases ?_ (fun i => ?_) j
  · exact congrFun h00 b
  · exact hs i b

theorem gsum_lin_cast (q K E : ℕ) (M : ℕ → Matrix m m F) (X : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    gsum q (E + 1) (lin K M) X (i.castSucc, a) = X (i.castSucc, a) ^ q - X (i.succ, a) := by
  simp only [gsum, Finset.sum_apply]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [lin_two_cast, zero_add, lin_one_cast, lin_zero_cast]
  simp [sub_eq_add_neg]

theorem gsum_lin_last (q K E : ℕ) (M : ℕ → Matrix m m F) (x : m → F) (a : m) :
    gsum q E (lin K M) (fun r => x r.2 ^ q ^ (r.1 : ℕ)) (Fin.last K, a) = gsum q (K + E) M x a := by
  simp only [gsum, Finset.sum_apply]
  rw [Finset.sum_range_succ', show K + E + 1 = (K + 1) + E by ring, Finset.sum_range_add, add_comm]
  congr 1
  · rw [lin_zero_last, Finset.sum_range]
    simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [lin_succ_last, show k + 1 + K = K + 1 + k by ring]
    congr 1
    ext b
    simp only [Fin.val_last]
    rw [← pow_mul, ← pow_add, show K + (k + 1) = K + 1 + k by omega]

theorem card_lin (q K E : ℕ) (M : ℕ → Matrix m m F) :
    Nat.card {x : m → F // Integral x ∧ gsum q (K + (E + 1)) M x = 0} =
      Nat.card {X : Fin (K + 1) × m → F // Integral X ∧ gsum q (E + 1) (lin K M) X = 0} := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨fun r => x.1 r.2 ^ q ^ (r.1 : ℕ), ?_, ?_⟩) ⟨?_, ?_⟩)
  · intro r
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (x.2.1 _)
  · funext ⟨j, a⟩
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [gsum_lin_last, x.2.2]; rfl
    · rw [gsum_lin_cast]
      simp [pow_succ, pow_mul]
  · intro x y hxy
    ext a
    have := congrFun (congrArg Subtype.val hxy) (0, a)
    simpa using this
  · rintro ⟨X, hX, hX0⟩
    have key : X = fun r => X (0, r.2) ^ q ^ (r.1 : ℕ) := by
      funext ⟨j, a⟩
      induction j using Fin.induction with
      | zero => simp
      | succ i ih =>
        have := congrFun hX0 (i.castSucc, a)
        rw [gsum_lin_cast, Pi.zero_apply, sub_eq_zero] at this
        rw [← this, ih]
        simp [pow_succ, pow_mul]
    refine ⟨⟨fun a => X (0, a), fun a => hX _, ?_⟩, Subtype.ext key.symm⟩
    funext a
    rw [← gsum_lin_last, ← key, hX0]; rfl

theorem glCount_of_one : ∀ N : ℕ, 1 ≤ N → GLCount 1 → GLCount N := by
  intro N hN h1 F _ _ _ _ p _ _ m _ _ e D he hD M hM hdet
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
  obtain ⟨E, rfl⟩ : ∃ E, D = K + (E + 1) := ⟨D - K - 1, by omega⟩
  rw [card_lin, h1 F p (Fin (K + 1) × m) e (E + 1) he (by omega) (lin K M) (lin_normal K M hM) (lin_det K M hdet)]
  simp [mul_comm]

end GlobalTheory.PMonE.LinCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemIntegralSurjectivityOfOne
section
noncomputable section

namespace GlobalTheory.PMonE

open Finset Matrix

section Lower

variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]

def lowerOrder (N : ℕ) (M : ℕ → Matrix m m F) (n : ℕ) : Matrix (m ⊕ m) (m ⊕ m) F :=
  fromBlocks (if n = N then 1 else 0) (if n + 1 = N then -1 else 0) (if n = 0 then M 0 else 0) (M (n + 1))

omit [Fintype m] in
theorem norm_one_apply_le (i j : m) : ‖(1 : Matrix m m F) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

omit [Fintype m] in
theorem lowerOrder_normal {N : ℕ} (hN : 1 ≤ N) {M : ℕ → Matrix m m F} (hM : Normal (N + 1) M) :
    Normal N (lowerOrder N M) := by
  constructor
  · intro n i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [lowerOrder, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    · split_ifs
      · exact norm_one_apply_le i j
      · simp
    · split_ifs
      · rw [Matrix.neg_apply, norm_neg]
        exact norm_one_apply_le i j
      · simp
    · split_ifs
      · exact hM.int 0 i j
      · simp
    · exact hM.int (n + 1) i j
  · have hN₀ : N ≠ 0 := by omega
    simp [lowerOrder, hN₀, hM.top]
  · intro n hn i j
    have h1 : n ≠ N := by omega
    have h2 : n + 1 ≠ N := by omega
    have h3 : n ≠ 0 := by omega
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [lowerOrder, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, ite_eq_right h1, ite_eq_right h2,
        ite_eq_right h3,
        Matrix.zero_apply, norm_zero, zero_lt_one]
    exact hM.small (n + 1) (by omega) i j

theorem gsum_lowerOrder_inl (q : ℕ) {K D : ℕ} (hD : K + 1 ≤ D) (M : ℕ → Matrix m m F) (z : m ⊕ m → F) (i : m) :
    gsum q D (lowerOrder (K + 1) M) z (Sum.inl i) = z (Sum.inl i) ^ q ^ (K + 1) - z (Sum.inr i) ^ q ^ K := by

  have h : ∀ n, (lowerOrder (K + 1) M n).mulVec (fun k => z k ^ q ^ n) (Sum.inl i) =
      (if n = K + 1 then z (Sum.inl i) ^ q ^ (K + 1) else 0) +
        (if n = K then -z (Sum.inr i) ^ q ^ K else 0) := by
    intro n
    simp only [lowerOrder, Matrix.fromBlocks_mulVec, Sum.elim_inl, Pi.add_apply, Function.comp_def]
    by_cases h1 : n = K + 1
    · subst h1
      simp
    · by_cases h2 : n = K
      · subst h2
        simp [Matrix.neg_mulVec]
      · have h3 : n ≠ K := h2
        simp [h1, h3]
  simp only [gsum, Finset.sum_apply, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
  rw [ite_eq_left (by omega), ite_eq_left (by omega), sub_eq_add_neg]

theorem gsum_lowerOrder_inr (q : ℕ) (N D : ℕ) (M : ℕ → Matrix m m F) (z : m ⊕ m → F)
    (hz : ∀ i, z (Sum.inr i) = z (Sum.inl i) ^ q) (i : m) :
    gsum q D (lowerOrder N M) z (Sum.inr i) = gsum q (D + 1) M (fun j => z (Sum.inl j)) i := by

  have h : ∀ n, (lowerOrder N M n).mulVec (fun k => z k ^ q ^ n) (Sum.inr i) =
      (if n = 0 then (M 0).mulVec (fun j => z (Sum.inl j) ^ q ^ 0) i else 0) +
        (M (n + 1)).mulVec (fun j => z (Sum.inl j) ^ q ^ (n + 1)) i := by
    intro n
    simp only [lowerOrder, Matrix.fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply, Function.comp_def, hz]
    congr 1
    · split_ifs with h0
      · subst h0
        rfl
      · simp
    · congr 2
      funext j
      rw [← pow_mul, ← pow_succ']
  simp only [gsum, Finset.sum_apply, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
  rw [Finset.sum_range_succ' _ (D + 1), ite_eq_left (by omega), add_comm]

end Lower

theorem glOnto_succ (K : ℕ) (H : GLOnto (K + 1)) : GLOnto (K + 2) := by
  intro F _ _ _ _ p _ _ m _ _ e D he hD M hM b hb
  obtain ⟨D, rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩

  obtain ⟨z, hzI, hzs⟩ := H F p (m ⊕ m) e D he (by omega) (lowerOrder (K + 1) M)
    (lowerOrder_normal (by omega) hM) (Sum.elim 0 b) (by
      intro k
      rcases k with k | k
      · simp
      · exact hb k)

  have hz : ∀ i, z (Sum.inr i) = z (Sum.inl i) ^ p ^ e := by
    intro i
    have h0 := congrFun hzs (Sum.inl i)
    rw [gsum_lowerOrder_inl (p ^ e) (by omega)] at h0
    simp only [Sum.elim_inl, Pi.zero_apply] at h0
    have hqK : (p ^ e) ^ K = p ^ (e * K) := (pow_mul p e K).symm
    have h1 : (z (Sum.inl i) ^ p ^ e - z (Sum.inr i)) ^ p ^ (e * K) = 0 := by
      rw [sub_pow_char_pow, ← hqK, ← pow_mul, ← pow_succ']
      exact h0
    exact (sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) |>.mp h1)).symm
  refine ⟨fun j => z (Sum.inl j), fun j => hzI (Sum.inl j), ?_⟩
  funext i
  rw [← gsum_lowerOrder_inr (p ^ e) (K + 1) D M z hz i, hzs]
  rfl

theorem glOnto_of_one : ∀ N : ℕ, 1 ≤ N → GLOnto 1 → GLOnto N := by
  intro N hN H
  induction N, hN using Nat.le_induction with
  | base => exact H
  | succ n hn ih =>
    obtain ⟨K, rfl⟩ : ∃ K, n = K + 1 := ⟨n - 1, by omega⟩
    exact glOnto_succ K ih

end GlobalTheory.PMonE

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangePolynomialAnnihilatesDescentStatement
section
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_polynomial_annihilates_descent : ∀ (Ks L0 KB WK ι : Type) [Field Ks] [Field L0] [Field KB] [Algebra Ks L0] [Algebra Ks KB] [AddCommGroup WK]
    [Module Ks WK] (rd : L0 →+* KB), (∀ a : Ks, rd (algebraMap Ks L0 a) = algebraMap Ks KB a) →
    ∀ (T0 : Module.End Ks WK) (s : Finset ι) (ρ : ι → Module.End Ks WK) (a : ι → L0) (q : L0[X]),
    (∀ z ∈ LinearMap.range (∑ g ∈ s, a g • LinearMap.baseChange L0 (ρ g)),
      Polynomial.aeval (LinearMap.baseChange L0 T0) q z = 0) →
    ∀ y ∈ LinearMap.range (∑ g ∈ s, rd (a g) • LinearMap.baseChange KB (ρ g)),
      Polynomial.aeval (LinearMap.baseChange KB T0) (q.map rd) y = 0 := by
  first | exact @GlobalTheory.baseChange_polynomial_kills_descent | exact GlobalTheory.baseChange_polynomial_kills_descent | (intros; apply GlobalTheory.baseChange_polynomial_kills_descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedPowersOrExistsValuationSubringDvd
section
open scoped NNReal
open Polynomial

namespace GlobalTheory

theorem pow_dvd_pow_mul_pow_of_homogeneous_relation {R : Type*} [CommRing R] (v x : R)
    (q : ℕ → R) (n N : ℕ) (h0 : IsUnit (q 0))
    (h : x ^ N * ∑ i ∈ Finset.range (n + 1), q i * v ^ i * x ^ (n - i) = 0) (j : ℕ) :
    v ^ j ∣ v ^ (N + n) * x ^ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j ≤ N + n
    · exact Dvd.dvd.mul_right (pow_dvd_pow v hj) _
    · obtain ⟨d, rfl⟩ : ∃ d, j = N + n + d := ⟨j - (N + n), by omega⟩
      rw [Finset.sum_range_succ'] at h
      have key : q 0 * (v ^ (N + n) * x ^ (N + n + d)) =
          - ∑ i ∈ Finset.range n,
            v ^ (N + n) * x ^ d * x ^ N * (q (i + 1) * v ^ (i + 1) * x ^ (n - (i + 1))) := by
        rw [← Finset.mul_sum]
        simp only [pow_zero, mul_one, Nat.sub_zero] at h
        linear_combination (v ^ (N + n) * x ^ d) * h
      rw [← h0.dvd_mul_left, key, dvd_neg]
      refine Finset.dvd_sum fun i hi => ?_
      have hi' : i < n := Finset.mem_range.1 hi
      obtain ⟨e, rfl⟩ : ∃ e, n = i + 1 + e := ⟨n - (i + 1), by omega⟩
      obtain ⟨w, hw⟩ := ih (N + e + d) (by omega)
      refine ⟨q (i + 1) * w, ?_⟩
      rw [Nat.add_sub_cancel_left]
      linear_combination (q (i + 1) * v ^ (i + 1)) * hw

theorem bounded_powers_or_exists_valuationSubring_dvd :
    ∀ (R : Type) [CommRing R] (u x : R) (M : ℕ), u ∈ nonZeroDivisors R →
      (∀ r, IsUnit (1 - u * r)) →
      (∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n) ∨
        ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L)
          (f : R →+* ↥V), f u ≠ 0 ∧ ¬ IsUnit (f u) ∧ f x ∣ f u ^ M := by
  intro R _ u x M hu hJ
  let T := Localization.Away (u * x)
  have hux : IsUnit (algebraMap R T (u * x)) := IsLocalization.Away.algebraMap_isUnit (u * x)
  rw [map_mul, IsUnit.mul_iff] at hux
  obtain ⟨huT, hxT⟩ := hux
  obtain ⟨y, hy⟩ := hxT.exists_right_inv
  let t : T := algebraMap R T u ^ M * y
  have ht : algebraMap R T x * t = algebraMap R T u ^ M := by
    simp only [t]
    linear_combination (algebraMap R T u ^ M) * hy
  let S := Algebra.adjoin R ({t} : Set T)
  by_cases hS : IsUnit (algebraMap R S u)
  · left
    obtain ⟨⟨z, hz⟩, hz1⟩ := hS.exists_right_inv
    have hz2 : algebraMap R T u * z = 1 := congrArg Subtype.val hz1
    have hz' := hz
    simp only [S] at hz'
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hz'
    obtain ⟨p, hp⟩ := hz'
    have hp' : aeval t p = z := hp
    set q : R[X] := 1 - C u * p with hq
    have hq0 : aeval t q = 0 := by
      simp [hq, hp', hz2]
    have hc : IsUnit (q.coeff 0) := by
      simpa [hq] using hJ (p.coeff 0)
    have hsum : algebraMap R T
        (∑ i ∈ Finset.range (q.natDegree + 1),
          q.coeff i * (u ^ M) ^ i * x ^ (q.natDegree - i)) = 0 := by
      have h1 : algebraMap R T x ^ q.natDegree * aeval t q = 0 := by rw [hq0, mul_zero]
      rw [aeval_eq_sum_range, Finset.mul_sum] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← h1]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ q.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hi'
      rw [he, Nat.add_sub_cancel_left, Algebra.smul_def]
      simp only [map_mul, map_pow]
      rw [← ht]
      ring
    obtain ⟨⟨_, N, rfl⟩, hN⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (u * x)) T _).1 hsum
    simp only [mul_pow, mul_assoc] at hN
    have hN' := (mul_left_mem_nonZeroDivisors_eq_zero_iff (pow_mem hu N)).1 hN
    refine ⟨M * (N + q.natDegree), fun j => ?_⟩
    rw [pow_mul, pow_mul]
    refine pow_dvd_pow_mul_pow_of_homogeneous_relation (u ^ M) x q.coeff _ N hc ?_ j
    simpa only [mul_assoc] using hN'
  · right
    obtain ⟨L, _, _, V, f, hf1, hf2⟩ := _root_.GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero S _ hS
    refine ⟨L, inferInstance, inferInstance, V, f.comp (algebraMap R S), ?_, hf1, ?_⟩
    · refine hf2 _ (mem_nonZeroDivisors_iff_right.2 fun s hs => ?_)
      have h1 : (s : T) * algebraMap R T u = 0 := congrArg Subtype.val hs
      exact Subtype.ext (huT.mul_left_eq_zero.1 h1)
    · refine ⟨f ⟨t, Algebra.self_mem_adjoin_singleton R t⟩, ?_⟩
      simp only [RingHom.comp_apply]
      rw [← map_mul, ← map_pow]
      congr 1
      exact Subtype.ext ht.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfDoubleAnnihilatorPairingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_le_of_double_annihilator_pairing : ∀ (O : Type) [CommRing O] (X Y E : Type) [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] [AddCommGroup E] [Module O E] [Finite X] (β : Y →ₗ[O] X →ₗ[O] E) (S : Submodule O X) (F : Finset Y) (Es : Finset E) (a : O), (∀ c, (∀ y, (∀ s ∈ S, β y s = 0) → β y c = 0) → c ∈ S) → (∀ y, (∀ s ∈ S, β y s = 0) → y ∈ F ∧ a • y = 0) → (∀ e : E, a • e = 0 → e ∈ Es) → Nat.card X ≤ Es.card ^ F.card * Nat.card S := by
  first | exact @GlobalTheory.card_le_of_double_annihilator | exact GlobalTheory.card_le_of_double_annihilator | (intros; apply GlobalTheory.card_le_of_double_annihilator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyMulLeftEqMapOfSpanningLatticeStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_mulLeft_eq_map_of_span_range_eq : ∀ (R F A S : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F] [CommRing A] [Algebra F A] [Algebra R A] [IsScalarTower R F A] [Module.Finite F A] [CommRing S] [Algebra R S] [Module.Finite R S] (ι : S →ₐ[R] A), Function.Injective ι → Submodule.span F (Set.range ι) = ⊤ → ∃ (n : ℕ) (b : Module.Basis (Fin n) R S), ∀ x : S, (LinearMap.mulLeft F (ι x)).charpoly = ((LinearMap.toMatrix b b (LinearMap.mulLeft R x)).charpoly).map (algebraMap R F) := by
  first | exact @GlobalTheory.charpoly_mulLeft_eq_map_of_spanning_lattice | exact GlobalTheory.charpoly_mulLeft_eq_map_of_spanning_lattice | (intros; apply GlobalTheory.charpoly_mulLeft_eq_map_of_spanning_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroSmulMemMapOfAevalMulEqZero
section
open scoped PowerSeries Pointwise
namespace GlobalTheory

theorem coeff_zero_smul_mem_map_of_aeval_mul_eq_zero : ∀ {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (T : Module.End O V) (Rp : Polynomial O), Polynomial.aeval T Rp * T = 0 → ∀ (Z : Submodule O V), (∀ z ∈ Z, T z ∈ Z) → ∀ w ∈ Z, w ∈ LinearMap.range T → Rp.coeff 0 • w ∈ Z.map T := by
  first
  | exact @_root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map
  | exact _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map
  | (apply _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map ..)

end GlobalTheory
end

