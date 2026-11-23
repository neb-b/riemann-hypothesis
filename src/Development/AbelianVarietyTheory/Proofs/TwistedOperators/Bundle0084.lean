module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ColumnDegreeLe

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarJacobianBlockDiagConjInvariant
section
noncomputable section
namespace GlobalTheory.PolarU.Conj
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
open scoped Kronecker

theorem conj_pow_of_mul_eq_one {n : Type} [Fintype n] [DecidableEq n] (A A' S : Matrix n n ℂ)
    (h : A * A' = 1) (m : ℕ) : (A * S * A') ^ m = A * S ^ m * A' := by
  have h' : A' * A = 1 := mul_eq_one_comm.mp h
  induction m with
  | zero => simp [h]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    calc A * S ^ m * A' * (A * S * A') = A * S ^ m * (A' * A) * S * A' := by
          simp only [mul_assoc]
      _ = A * (S ^ m * S) * A' := by rw [h', mul_one]; simp only [mul_assoc]

theorem conj_tsum_of_mul_eq_one {n : Type} [Fintype n] [DecidableEq n] (A A' : Matrix n n ℂ)
    (h : A * A' = 1) (f : ℕ → Matrix n n ℂ) :
    A * (∑' m, f m) * A' = ∑' m, A * f m * A' := by
  have h' : A' * A = 1 := mul_eq_one_comm.mp h
  by_cases hf : Summable f
  · rw [← hf.tsum_mul_left A, ← (hf.mul_left A).tsum_mul_right A']
  · have hg : ¬ Summable (fun m => A * f m * A') := by
      intro hg
      apply hf
      have hs := (hg.mul_left A').mul_right A
      refine hs.congr (fun m => ?_)
      rw [show A' * (A * f m * A') * A = (A' * A) * f m * (A' * A) by simp only [mul_assoc],
        h', one_mul, mul_one]
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hg]
    simp

theorem submatrix_mul_of_left {n : Type} [Fintype n] (P : n → Prop) [DecidablePred P]
    (A S : Matrix n n ℂ) (hA : ∀ i j, P i → ¬ P j → A i j = 0) :
    (A * S).submatrix (Subtype.val : {i // P i} → n) (Subtype.val : {i // P i} → n) =
      A.submatrix Subtype.val (Subtype.val : {i // P i} → n) *
        S.submatrix Subtype.val Subtype.val := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have key : ∀ k ∈ (Finset.univ : Finset n), A (i : n) k * S k (j : n) ≠ 0 → P k := by
    intro k _ hk
    by_contra hPk
    exact hk (by rw [hA _ _ i.2 hPk, zero_mul])
  rw [← Finset.sum_filter_of_ne key]
  exact Finset.sum_subtype _ (by simp) (fun k => A (i : n) k * S k (j : n))

theorem submatrix_mul_of_right {n : Type} [Fintype n] (P : n → Prop) [DecidablePred P]
    (S A : Matrix n n ℂ) (hA : ∀ i j, ¬ P i → P j → A i j = 0) :
    (S * A).submatrix (Subtype.val : {i // P i} → n) (Subtype.val : {i // P i} → n) =
      S.submatrix Subtype.val (Subtype.val : {i // P i} → n) *
        A.submatrix Subtype.val Subtype.val := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have key : ∀ k ∈ (Finset.univ : Finset n), S (i : n) k * A k (j : n) ≠ 0 → P k := by
    intro k _ hk
    by_contra hPk
    exact hk (by rw [hA _ _ hPk j.2, mul_zero])
  rw [← Finset.sum_filter_of_ne key]
  exact Finset.sum_subtype _ (by simp) (fun k => S (i : n) k * A k (j : n))

variable {p q : ℕ}

theorem kron_noMix {k l : Mat p q} (hk : IsKC k) (hl : IsKC l) (i j : Ix p q × Ix p q)
    (h : ¬ (sameBlock i.1 i.2 ↔ sameBlock j.1 j.2)) : (k ⊗ₖ lᵀ) i j = 0 := by
  simp only [Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  by_cases h1 : sameBlock i.1 j.1
  · have h2 : ¬ sameBlock j.2 i.2 := by
      intro h2
      apply h
      rcases i with ⟨a | a, b | b⟩ <;> rcases j with ⟨c | c, d | d⟩ <;> simp_all [sameBlock]
    rw [hl _ _ h2, mul_zero]
  · rw [hk _ _ h1, zero_mul]

theorem kron_mul_eq_one {k k' : Mat p q} (h : k * k' = 1) :
    (k ⊗ₖ k'ᵀ) * (k' ⊗ₖ kᵀ) = 1 := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul, h, Matrix.transpose_one,
    Matrix.one_kronecker_one]

theorem adMat_conj {k k' : Mat p q} (h : k * k' = 1) (Y : Mat p q) :
    adMat (k * Y * k') = (k ⊗ₖ k'ᵀ) * adMat Y * (k' ⊗ₖ kᵀ) := by
  have h1 : k'ᵀ * kᵀ = 1 := by rw [← Matrix.transpose_mul, h, Matrix.transpose_one]
  unfold adMat
  rw [Matrix.mul_sub, Matrix.sub_mul]
  simp only [← Matrix.mul_kronecker_mul]
  simp [h, h1, Matrix.transpose_mul, mul_assoc]

theorem sinhcAd_conj {k k' : Mat p q} (h : k * k' = 1) (Y : Mat p q) :
    sinhcAd (k * Y * k') = (k ⊗ₖ k'ᵀ) * sinhcAd Y * (k' ⊗ₖ kᵀ) := by
  unfold sinhcAd
  rw [adMat_conj h, conj_tsum_of_mul_eq_one _ _ (kron_mul_eq_one h)]
  refine tsum_congr (fun j => ?_)
  rw [conj_pow_of_mul_eq_one _ _ _ (kron_mul_eq_one h), Matrix.mul_smul, Matrix.smul_mul]

theorem polJ_conj (p q : ℕ) (k k' Y : Mat p q) (h : k * k' = 1) (hk : IsKC k) (hk' : IsKC k') :
    polJ (k * Y * k') = polJ Y := by
  unfold polJ
  rw [sinhcAd_conj h]
  have hK : ∀ i j : Ix p q × Ix p q, ¬ sameBlock i.1 i.2 → ¬ ¬ sameBlock j.1 j.2 →
      (k ⊗ₖ k'ᵀ) i j = 0 := fun i j hi hj => kron_noMix hk hk' i j (by tauto)
  have hK' : ∀ i j : Ix p q × Ix p q, ¬ ¬ sameBlock i.1 i.2 → ¬ sameBlock j.1 j.2 →
      (k' ⊗ₖ kᵀ) i j = 0 := fun i j hi hj => kron_noMix hk' hk i j (by tauto)
  have e1 : ((k ⊗ₖ k'ᵀ) * sinhcAd Y * (k' ⊗ₖ kᵀ)).submatrix (Subtype.val : PIx p q → _)
      Subtype.val = ((k ⊗ₖ k'ᵀ) * sinhcAd Y).submatrix (Subtype.val : PIx p q → _) Subtype.val *
        (k' ⊗ₖ kᵀ).submatrix Subtype.val Subtype.val :=
    submatrix_mul_of_right (fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2) _ _ hK'
  have e2 : ((k ⊗ₖ k'ᵀ) * sinhcAd Y).submatrix (Subtype.val : PIx p q → _) Subtype.val =
      (k ⊗ₖ k'ᵀ).submatrix (Subtype.val : PIx p q → _) Subtype.val *
        (sinhcAd Y).submatrix Subtype.val Subtype.val :=
    submatrix_mul_of_left (fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2) _ _ hK
  have e3 : ((k ⊗ₖ k'ᵀ) * (k' ⊗ₖ kᵀ)).submatrix (Subtype.val : PIx p q → _) Subtype.val =
      (k ⊗ₖ k'ᵀ).submatrix (Subtype.val : PIx p q → _) Subtype.val *
        (k' ⊗ₖ kᵀ).submatrix Subtype.val Subtype.val :=
    submatrix_mul_of_left (fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2) _ _ hK
  rw [kron_mul_eq_one h, Matrix.submatrix_one _ Subtype.val_injective] at e3
  have e5 := congrArg Matrix.det e3
  rw [Matrix.det_one, Matrix.det_mul] at e5
  rw [e1, e2, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← e5, one_mul]

end GlobalTheory.PolarU.Conj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdSinhcRootValueOfMatrixUnitP
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU.RootProd

theorem shc_neg' (x : ℝ) : shc (-x) = shc x := by
  unfold shc
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg (neg_ne_zero.mpr hx), if_neg hx, Real.sinh_neg, neg_div_neg_eq]

theorem shc_zero' : shc 0 = 1 := by
  unfold shc
  exact if_pos rfl

theorem prod_square (n : ℕ) (F : ℕ → ℕ → ℝ) :
    ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, F i j =
      (∏ i ∈ Finset.range n, F i i) *
        ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, if i < j then F i j * F j i else 1 := by

  have split3 : ∀ i j, F i j = (if j = i then F i i else 1) * (if i < j then F i j else 1) *
      (if j < i then F i j else 1) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, hij.ne', not_lt.mpr hij.le]
    · simp
    · simp [hji, hji.ne, not_lt.mpr hji.le]
  have row : ∀ i ∈ Finset.range n, (∏ j ∈ Finset.range n, F i j) =
      F i i * ((∏ j ∈ Finset.range n, if i < j then F i j else 1) *
        ∏ j ∈ Finset.range n, if j < i then F i j else 1) := by
    intro i hi
    have hd : (∏ j ∈ Finset.range n, if j = i then F i i else 1) = F i i := by
      rw [Finset.prod_ite_eq']
      exact if_pos hi
    rw [← Finset.prod_mul_distrib, ← hd, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [← mul_assoc]; exact split3 i j

  have below : (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, if j < i then F i j else 1) =
      ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, if i < j then F j i else 1 :=
    Finset.prod_comm
  rw [Finset.prod_congr rfl row, Finset.prod_mul_distrib, Finset.prod_mul_distrib, below,
    ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem prod_PIx (p q : ℕ) (h : ℕ → ℝ) :
    ∏ ab : PIx p q, shc (rootP h ab.1) =
      ∏ i ∈ Finset.range p, ∏ j ∈ Finset.range q,
        shc (cutH p q h i - cutH p q h j) * shc (cutH p q h i + cutH p q h j) := by

  rw [← Finset.prod_subtype (Finset.univ.filter fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2)
    (fun ab => by simp) (fun ab => shc (rootP h ab))]
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  simp only [Fintype.prod_sum_type, sameBlock, not_true_eq_false, not_false_eq_true, if_false,
    if_true, Finset.prod_const_one, one_mul, mul_one, rootP, Sum.isLeft_inl, Sum.isLeft_inr,
    posIx, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true]
  simp_rw [Finset.prod_range, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by rw [add_comm]

theorem prod_rect (m d : ℕ) (h c : ℕ → ℝ) (hc : ∀ n, c n = if n < m then h n else 0) :
    ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range (m + d), shc (c i - c j) * shc (c i + c j) =
      (∏ i ∈ Finset.range m, shc (2 * h i) * shc (h i) ^ (2 * d)) *
        ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m,
          if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := by
  have hin : ∀ i ∈ Finset.range m, c i = h i := fun i hi => by
    rw [hc, if_pos (Finset.mem_range.mp hi)]
  have hout : ∀ k, c (m + k) = 0 := fun k => by
    rw [hc, if_neg (by omega)]

  have swap : ∀ a b : ℝ, shc (b - a) * shc (b + a) = shc (a - b) * shc (a + b) := fun a b => by
    rw [show b - a = -(a - b) by ring, shc_neg', add_comm b a]

  have row : ∀ i ∈ Finset.range m,
      (∏ j ∈ Finset.range (m + d), shc (c i - c j) * shc (c i + c j)) =
        (∏ j ∈ Finset.range m, shc (h i - h j) * shc (h i + h j)) * shc (h i) ^ (2 * d) := by
    intro i hi
    rw [Finset.prod_range_add]
    congr 1
    · exact Finset.prod_congr rfl fun j hj => by rw [hin i hi, hin j hj]
    · simp only [hout, hin i hi, sub_zero, add_zero]
      rw [Finset.prod_const, Finset.card_range, ← pow_two, ← pow_mul]
  have diag : ∀ i, shc (h i - h i) * shc (h i + h i) = shc (2 * h i) := fun i => by
    rw [sub_self, shc_zero', one_mul, two_mul]
  have off : ∀ i j, (if i < j then shc (h i - h j) * shc (h i + h j) * (shc (h j - h i) * shc (h j + h i))
      else 1) = if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := fun i j => by
    rw [swap (h i) (h j), sq]
  rw [Finset.prod_congr rfl row, Finset.prod_mul_distrib,
    prod_square m (fun i j => shc (h i - h j) * shc (h i + h j))]
  simp only [diag]
  rw [Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => off i j]
  ring

theorem prod_shc_rootP : ∀ (p q : ℕ) (h : ℕ → ℝ), ∏ ab : PIx p q, shc (rootP h ab.1) = (∏ i ∈ Finset.range (min p q), shc (2 * h i) * shc (h i) ^ (2 * (max p q - min p q))) * ∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q), if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := by
  intro p q h
  have hm : min p q + (max p q - min p q) = max p q := Nat.add_sub_cancel' min_le_max
  have swap : ∀ a b : ℝ, shc (b - a) * shc (b + a) = shc (a - b) * shc (a + b) := fun a b => by
    rw [show b - a = -(a - b) by ring, shc_neg', add_comm b a]
  rw [← prod_rect (min p q) (max p q - min p q) h (cutH p q h) (fun n => rfl), hm, prod_PIx]
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq, max_eq_right hpq]
  ·
    rw [min_eq_right hqp, max_eq_left hqp, Finset.prod_comm]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => swap _ _

end GlobalTheory.PolarU.RootProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowColWeightsAgree
section
noncomputable section

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm.BlockWeights

def extZero {p : ℕ} (a : Fin p → ℕ) (i : ℕ) : ℕ := if h : i < p then a ⟨i, h⟩ else 0

theorem sum_range_extZero {p : ℕ} (a : Fin p → ℕ) (i : ℕ) :
    ∑ j ∈ Finset.range i, extZero a j =
      ∑ b ∈ Finset.univ.filter (fun b : Fin p => (b : ℕ) < i), a b := by
  induction i with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : n < p
    · have hset : Finset.univ.filter (fun b : Fin p => (b : ℕ) < n + 1) =
          insert ⟨n, h⟩ (Finset.univ.filter (fun b : Fin p => (b : ℕ) < n)) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [hset, Finset.sum_insert (by simp), add_comm]
      simp only [extZero, dif_pos h]
    · have hset : Finset.univ.filter (fun b : Fin p => (b : ℕ) < n + 1) =
          Finset.univ.filter (fun b : Fin p => (b : ℕ) < n) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [hset]
      simp only [extZero, dif_neg h, add_zero]

theorem partial_sum_le {σ : Type} [DecidableEq σ] {p r : ℕ} (z : Fin p × Fin r → σ)
    (hz : Function.Injective z) (P : MvPolynomial σ ℂ) (a : Fin p → ℕ) (a' : Fin r → ℕ)
    (hP : P ≠ 0) (hrow : ∀ i j : Fin p, i < j → rowOp ℂ z i j P = 0)
    (ha : ∀ i, rowOp ℂ z i i P = (a i : ℂ) • P) (ha' : ∀ i, colOp ℂ z i i P = (a' i : ℂ) • P)
    (i : ℕ) :
    ∑ j ∈ Finset.range i, extZero a' j ≤ ∑ j ∈ Finset.range i, extZero a j := by

  have hinv : ∀ b c : Fin p, b < c → ∀ t : ℂ,
      bind₁ (fun s => X s + ∑ k, if s = z (c, k) then C t * X (z (b, k)) else 0) P = P := by
    intro b c hbc t
    have hw : Function.Injective (fun k : Fin r => z (c, k)) :=
      fun k l h => congrArg Prod.snd (hz h)
    have huw : ∀ k l : Fin r, z (b, k) ≠ z (c, l) := by
      intro k l h
      exact (ne_of_lt hbc) (congrArg Prod.fst (hz h))
    have hT := GlobalTheory.rowAdd_invariant_iff (K := ℂ) (fun k : Fin r => z (b, k))
      (fun k : Fin r => z (c, k)) hw huw P
    have h0 : ∑ k, X (z (b, k)) * pderiv (z (c, k)) P = 0 := by
      rw [← GlobalTheory.Capelli.rowOp_apply]
      exact hrow b c hbc
    have h23 := hT.out 2 3
    exact h23.mpr h0 t

  have hrowdeg : ∀ b, ∀ m ∈ P.support, ∑ k, m (z (b, k)) = a b := by
    intro b m hm
    exact_mod_cast (GlobalTheory.JointHarm.rowOp_eq_smul_iff z b P _).mp (ha b) m hm
  have hcoldeg : ∀ k, ∀ m ∈ P.support, ∑ b, m (z (b, k)) = a' k := by
    intro k m hm
    exact_mod_cast (GlobalTheory.JointHarm.colOp_eq_smul_iff z k P _).mp (ha' k) m hm
  obtain ⟨m, hm⟩ : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hP
  have key := GlobalTheory.column_degree_le z hz P a hrowdeg hinv
    (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)) m hm
  have hcard : (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)).card ≤ i := by
    calc (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)).card
        = ((Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)).map Fin.valEmbedding).card :=
          (Finset.card_map _).symm
      _ ≤ (Finset.range i).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Fin.valEmbedding_apply] at hx
          obtain ⟨k, hk, hkx⟩ := hx
          rw [Finset.mem_range, ← hkx]
          exact hk
      _ = i := Finset.card_range i
  rw [sum_range_extZero, sum_range_extZero]
  calc ∑ k ∈ Finset.univ.filter (fun k : Fin r => (k : ℕ) < i), a' k
      = ∑ k ∈ Finset.univ.filter (fun k : Fin r => (k : ℕ) < i), ∑ b, m (z (b, k)) :=
        Finset.sum_congr rfl (fun k _ => (hcoldeg k m hm).symm)
    _ = ∑ b, ∑ k ∈ Finset.univ.filter (fun k : Fin r => (k : ℕ) < i), m (z (b, k)) :=
        Finset.sum_comm
    _ ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin p =>
          (b : ℕ) < (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)).card), a b := key
    _ ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin p => (b : ℕ) < i), a b := by
        apply Finset.sum_le_sum_of_subset
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        omega

theorem row_col_weights_agree : ∀ (σ : Type) [DecidableEq σ] (p r : ℕ) (z : Fin p × Fin r → σ), Function.Injective z → ∀ (P : MvPolynomial σ ℂ) (a : Fin p → ℕ) (a' : Fin r → ℕ), P ≠ 0 → Antitone a → (∀ i j : Fin p, i < j → rowOp ℂ z i j P = 0) → (∀ i j : Fin r, i < j → colOp ℂ z i j P = 0) → (∀ i, rowOp ℂ z i i P = (a i : ℂ) • P) → (∀ i, colOp ℂ z i i P = (a' i : ℂ) • P) → ∃ α : ℕ → ℕ, Antitone α ∧ (∀ i, min p r ≤ i → α i = 0) ∧ (∀ i : Fin p, a i = α i) ∧ ∀ i : Fin r, a' i = α i := by
  intro σ _ p r z hz P a a' hP hanti hrow hcol ha ha'
  have h1 : ∀ i, ∑ j ∈ Finset.range i, extZero a' j ≤ ∑ j ∈ Finset.range i, extZero a j :=
    partial_sum_le z hz P a a' hP hrow ha ha'

  have h2 : ∀ i, ∑ j ∈ Finset.range i, extZero a j ≤ ∑ j ∈ Finset.range i, extZero a' j := by
    have hz' : Function.Injective (fun w : Fin r × Fin p => z w.swap) :=
      hz.comp Prod.swap_injective
    have e : ∀ k l : Fin r,
        rowOp ℂ (fun w : Fin r × Fin p => z w.swap) k l = colOp ℂ z k l :=
      fun k l => GlobalTheory.Capelli.rowOp_eq_colOp _ k l
    have e' : ∀ b c : Fin p,
        colOp ℂ (fun w : Fin r × Fin p => z w.swap) b c = rowOp ℂ z b c :=
      fun b c => (GlobalTheory.Capelli.rowOp_eq_colOp z b c).symm
    exact partial_sum_le (fun w : Fin r × Fin p => z w.swap) hz' P a' a hP
      (fun k l hkl => by rw [e]; exact hcol k l hkl) (fun k => by rw [e]; exact ha' k)
      (fun b => by rw [e']; exact ha b)
  have hsum : ∀ i, ∑ j ∈ Finset.range i, extZero a j = ∑ j ∈ Finset.range i, extZero a' j :=
    fun i => le_antisymm (h2 i) (h1 i)

  have heq : ∀ j, extZero a j = extZero a' j := by
    intro j
    have hj := hsum (j + 1)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hsum j] at hj
    omega
  refine ⟨extZero a, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    unfold extZero
    by_cases hj : j < p
    · rw [dif_pos hj, dif_pos (lt_of_le_of_lt hij hj)]
      exact hanti (Fin.mk_le_mk.mpr hij)
    · rw [dif_neg hj]
      exact Nat.zero_le _
  · intro i hi
    by_cases hp : p ≤ i
    · simp [extZero, show ¬ i < p by omega]
    · rw [heq i]
      simp [extZero, show ¬ i < r by omega]
  · intro i
    simp [extZero]
  · intro i
    rw [heq]
    simp [extZero]

end GlobalTheory.JointHarm.BlockWeights
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdjointApplyMatrixUpperRightBlockElementP
section
noncomputable section
namespace GlobalTheory.PolarU.SinhcPres
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

variable {p q : ℕ}

theorem ad_sq_pY (B C : Fin p → Fin q → ℂ) : ∃ D,
    pY B * (pY B * pY C - pY C * pY B) - (pY B * pY C - pY C * pY B) * pY B = pY D := by
  refine ⟨fun i j => (pY B * (pY B * pY C - pY C * pY B) - (pY B * pY C - pY C * pY B) * pY B)
    (Sum.inl i) (Sum.inr j), ?_⟩
  have hh : (pY B * (pY B * pY C - pY C * pY B) - (pY B * pY C - pY C * pY B) * pY B)ᴴ =
      pY B * (pY B * pY C - pY C * pY B) - (pY B * pY C - pY C * pY B) * pY B := by
    simp only [conjTranspose_sub, conjTranspose_mul, pY_conjTranspose]
    noncomm_ring
  ext a b
  rcases a with i | i <;> rcases b with j | j
  · simp [pY, pOf, Matrix.mul_apply, Fintype.sum_sum_type]
  · simp only [pY, pOf, fromBlocks_apply₁₂, of_apply]
  · have := congrFun (congrFun hh (Sum.inr i)) (Sum.inl j)
    rw [← this]
    rfl
  · simp [pY, pOf, Matrix.mul_apply, Fintype.sum_sum_type]

theorem adMat_pow_pY (B C : Fin p → Fin q → ℂ) (k : ℕ) : ∃ D,
    adMat (pY B) ^ (2 * k) *ᵥ vecM (pY C) = vecM (pY D) := by
  induction k with
  | zero => exact ⟨C, by simp⟩
  | succ k ih =>
    obtain ⟨D, hD⟩ := ih
    obtain ⟨E, hE⟩ := ad_sq_pY B D
    refine ⟨E, ?_⟩
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ', pow_succ', ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hD, adMat_mulVec, adMat_mulVec, hE]

theorem summable_sinhc {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    Summable fun k : ℕ => (((2 * k + 1).factorial : ℂ)⁻¹) • A ^ (2 * k) := by
  open scoped Matrix.Norms.Operator in
  refine Summable.of_norm_bounded (g := fun k : ℕ => ‖((k.factorial : ℂ)⁻¹) • (A ^ 2) ^ k‖)
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) (A ^ 2)) fun k => ?_
  rw [norm_smul, norm_smul, ← pow_mul, norm_inv, norm_inv, Complex.norm_natCast,
    Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine inv_anti₀ (by exact_mod_cast k.factorial_pos) ?_
  exact_mod_cast Nat.factorial_le (by omega)

theorem hasSum_sAd (Y V : Mat p q) (a b : Ix p q) :
    HasSum (fun k : ℕ => (((2 * k + 1).factorial : ℂ)⁻¹) * (adMat Y ^ (2 * k) *ᵥ vecM V) (a, b))
      (sAd Y V a b) := by
  have h := (summable_sinhc (adMat Y)).hasSum
  let f : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ →+ ℂ :=
    { toFun := fun M => (M *ᵥ vecM V) (a, b)
      map_zero' := by simp
      map_add' := fun M N => by simp [Matrix.add_mulVec] }
  have hf : Continuous f := by
    show Continuous fun M : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ => (M *ᵥ vecM V) (a, b)
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have h2 := h.map f hf
  convert (preTransparency := .reducible) h2 using 1
  · funext k
    simp [f, Matrix.smul_mulVec]
  · rfl

theorem sAd_pY : ∀ (p q : ℕ) (B C : Fin p → Fin q → ℂ),
    sAd (pY B) (pY C) = pY (sP (pY B) C) := by
  intro p q B C
  choose D hD using adMat_pow_pY B C
  have h := hasSum_sAd (pY B) (pY C)
  simp only [hD, vecM] at h
  ext a b
  rcases a with i | i <;> rcases b with j | j
  · have := h (Sum.inl i) (Sum.inl j)
    simp only [pY, pOf, fromBlocks_apply₁₁, Matrix.zero_apply, mul_zero] at this ⊢
    exact this.unique hasSum_zero
  · rfl
  · have h1 := h (Sum.inr i) (Sum.inl j)
    have h2 := (h (Sum.inl j) (Sum.inr i)).star
    show _ = star (sAd (pY B) (pY C) (Sum.inl j) (Sum.inr i))
    refine h1.unique ?_
    convert h2 using 2 with k
    simp [pY, pOf]
  · have := h (Sum.inr i) (Sum.inr j)
    simp only [pY, pOf, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero] at this ⊢
    exact this.unique hasSum_zero

end GlobalTheory.PolarU.SinhcPres
end
end

