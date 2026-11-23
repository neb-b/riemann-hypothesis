module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemPreparationNormalFormOne
section
noncomputable section

namespace GlobalTheory.PMonE

open Finset

section Prep

variable {F : Type} [NormedField F] {m : Type} [Fintype m]

def PrepBd (c : ℝ) (X : Matrix m m F) : Prop := ∀ i j, ‖X i j‖ ≤ c

noncomputable def prepV (q : ℕ) (M : ℕ → Matrix m m F) (A : Matrix m m F) (k : ℕ) : ℕ → Matrix m m F :=
  Nat.rec (motive := fun _ => ℕ → Matrix m m F) (fun _ => 0)
    (fun _ V n => M (n + 1) + V (n + 1) * A.map (fun a => a ^ q ^ (n + 1))) k

theorem prepV_zero (q : ℕ) (M : ℕ → Matrix m m F) (A : Matrix m m F) (n : ℕ) : prepV q M A 0 n = 0 := rfl

theorem prepV_succ (q : ℕ) (M : ℕ → Matrix m m F) (A : Matrix m m F) (k n : ℕ) :
    prepV q M A (k + 1) n = M (n + 1) + prepV q M A k (n + 1) * A.map (fun a => a ^ q ^ (n + 1)) := rfl

variable [IsUltrametricDist F]

omit [Fintype m] in
theorem PrepBd.add {c : ℝ} {X Y : Matrix m m F} (hX : PrepBd c X) (hY : PrepBd c Y) : PrepBd c (X + Y) :=
  fun i j => (IsUltrametricDist.norm_add_le_max (X i j) (Y i j)).trans (max_le (hX i j) (hY i j))

omit [Fintype m] [IsUltrametricDist F] in
theorem PrepBd.neg {c : ℝ} {X : Matrix m m F} (hX : PrepBd c X) : PrepBd c (-X) :=
  fun i j => by simpa using hX i j

omit [Fintype m] [IsUltrametricDist F] in
theorem PrepBd.mono {c d : ℝ} {X : Matrix m m F} (hX : PrepBd c X) (h : c ≤ d) : PrepBd d X :=
  fun i j => (hX i j).trans h

theorem PrepBd.mul {c d : ℝ} {X Y : Matrix m m F} (hc : 0 ≤ c) (hd : 0 ≤ d) (hX : PrepBd c X) (hY : PrepBd d Y) :
    PrepBd (c * d) (X * Y) := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc hd) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hX i k) (hY k j) (norm_nonneg _) hc

omit [Fintype m] [IsUltrametricDist F] in
theorem PrepBd.map_pow {X : Matrix m m F} (hX : PrepBd 1 X) (N : ℕ) : PrepBd 1 (X.map (fun a => a ^ N)) := by
  intro i j
  rw [Matrix.map_apply, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hX i j)

theorem prepV_bd {q D : ℕ} {M : ℕ → Matrix m m F} {δ : ℝ} (hδ : 0 ≤ δ)
    (hM : ∀ n, 2 ≤ n → n ≤ D → PrepBd δ (M n)) {A : Matrix m m F} (hA : PrepBd 1 A) :
    ∀ k n, 1 ≤ n → n + k ≤ D → PrepBd δ (prepV q M A k n) := by
  intro k
  induction k with
  | zero => intro n _ _ i j; simpa [prepV_zero] using hδ
  | succ k ih =>
    intro n hn hk
    rw [prepV_succ]
    refine (hM _ (by omega) (by omega)).add ?_
    simpa using PrepBd.mul hδ zero_le_one (ih (n + 1) (by omega) (by omega)) (hA.map_pow _)

omit [Fintype m] in
theorem PrepBd.map_pow_sub (p : ℕ) [Fact p.Prime] [CharP F p] (e n : ℕ) {A B : Matrix m m F} {ε : ℝ}
    (hA : PrepBd 1 A) (hB : PrepBd 1 B) (h : PrepBd ε (A - B)) :
    PrepBd ε (A.map (fun a => a ^ (p ^ e) ^ n) - B.map (fun a => a ^ (p ^ e) ^ n)) := by
  intro i j
  have h1 : ‖A i j - B i j‖ ≤ 1 := by
    have := (hA.add hB.neg) i j
    simpa [sub_eq_add_neg] using this
  have h2 : ‖A i j - B i j‖ ≤ ε := h i j
  rw [Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← pow_mul, ← sub_pow_char_pow, norm_pow]
  exact (pow_le_of_le_one (norm_nonneg _) h1 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).trans h2

theorem prepV_sub_bd (p : ℕ) [Fact p.Prime] [CharP F p] {e D : ℕ} {M : ℕ → Matrix m m F} {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hε : 0 ≤ ε) (hM : ∀ n, 2 ≤ n → n ≤ D → PrepBd δ (M n)) {A B : Matrix m m F} (hA : PrepBd 1 A)
    (hB : PrepBd 1 B) (h : PrepBd ε (A - B)) :
    ∀ k n, 1 ≤ n → n + k ≤ D → PrepBd (δ * ε) (prepV (p ^ e) M A k n - prepV (p ^ e) M B k n) := by
  intro k
  induction k with
  | zero => intro n _ _ i j; simpa [prepV_zero] using mul_nonneg hδ hε
  | succ k ih =>
    intro n hn hk
    rw [prepV_succ, prepV_succ]
    have e1 : M (n + 1) + prepV (p ^ e) M A k (n + 1) * A.map (fun a => a ^ (p ^ e) ^ (n + 1)) -
        (M (n + 1) + prepV (p ^ e) M B k (n + 1) * B.map (fun a => a ^ (p ^ e) ^ (n + 1))) =
        (prepV (p ^ e) M A k (n + 1) - prepV (p ^ e) M B k (n + 1)) * A.map (fun a => a ^ (p ^ e) ^ (n + 1)) +
        prepV (p ^ e) M B k (n + 1) *
          (A.map (fun a => a ^ (p ^ e) ^ (n + 1)) - B.map (fun a => a ^ (p ^ e) ^ (n + 1))) := by
      rw [Matrix.sub_mul, Matrix.mul_sub]; abel
    rw [e1]
    refine PrepBd.add ?_ ?_
    · simpa using PrepBd.mul (mul_nonneg hδ hε) zero_le_one (ih (n + 1) (by omega) (by omega)) (hA.map_pow _)
    · exact PrepBd.mul hδ hε (prepV_bd hδ hM hB k (n + 1) (by omega) (by omega))
        (PrepBd.map_pow_sub p e _ hA hB h)

theorem prep_fixed [CompleteSpace F] {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) (M0 : Matrix m m F) (h0 : PrepBd 1 M0)
    (W : Matrix m m F → Matrix m m F) (hW : ∀ A, PrepBd 1 A → PrepBd δ (W A))
    (hW2 : ∀ A B ε, 0 ≤ ε → PrepBd 1 A → PrepBd 1 B → PrepBd ε (A - B) → PrepBd (δ * ε) (W A - W B)) :
    ∃ A, PrepBd 1 A ∧ A = -M0 - W A * A := by
  let s : Set (m → m → F) := {A | ∀ i j, ‖A i j‖ ≤ 1}
  let f : (m → m → F) → (m → m → F) := fun A => fun i j => (-M0 - W (Matrix.of A) * (Matrix.of A)) i j
  have hs : IsClosed s := by
    simp only [s, Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
  have hf : Set.MapsTo f s s := by
    intro A hA
    have hA' : PrepBd 1 (Matrix.of A) := hA
    have : PrepBd 1 (-M0 - W (Matrix.of A) * (Matrix.of A)) := by
      rw [sub_eq_add_neg]
      refine h0.neg.add (PrepBd.neg ?_)
      exact (PrepBd.mul hδ zero_le_one (hW _ hA') hA').mono (by simpa using hδ1.le)
    exact this
  have hc : ContractingWith ⟨δ, hδ⟩ (hf.restrict f s s) := by
    refine ⟨hδ1, LipschitzWith.of_dist_le_mul fun A B => ?_⟩
    have hA' : PrepBd 1 (Matrix.of A.1) := A.2
    have hB' : PrepBd 1 (Matrix.of B.1) := B.2
    have hε : 0 ≤ dist A B := dist_nonneg
    have hAB : PrepBd (dist A B) (Matrix.of A.1 - Matrix.of B.1) := by
      intro i j
      rw [Matrix.sub_apply, Matrix.of_apply, Matrix.of_apply, ← dist_eq_norm, Subtype.dist_eq]
      exact (dist_le_pi_dist _ _ j).trans (dist_le_pi_dist A.1 B.1 i)
    have key : PrepBd (δ * dist A B) ((-M0 - W (Matrix.of A.1) * (Matrix.of A.1)) -
        (-M0 - W (Matrix.of B.1) * (Matrix.of B.1))) := by
      have e1 : (-M0 - W (Matrix.of A.1) * (Matrix.of A.1)) - (-M0 - W (Matrix.of B.1) * (Matrix.of B.1)) =
          -((W (Matrix.of A.1) - W (Matrix.of B.1)) * (Matrix.of A.1) +
            W (Matrix.of B.1) * (Matrix.of A.1 - Matrix.of B.1)) := by
        rw [Matrix.sub_mul, Matrix.mul_sub]; abel
      rw [e1]
      refine PrepBd.neg (PrepBd.add ?_ ?_)
      · simpa using PrepBd.mul (mul_nonneg hδ hε) zero_le_one (hW2 _ _ _ hε hA' hB' hAB) hA'
      · exact PrepBd.mul hδ hε (hW _ hB') hAB
    change dist (f A.1) (f B.1) ≤ δ * dist A B
    refine (dist_pi_le_iff (mul_nonneg hδ hε)).2 fun i => (dist_pi_le_iff (mul_nonneg hδ hε)).2 fun j => ?_
    rw [dist_eq_norm]
    exact key i j
  obtain ⟨y, hy, hfix, -⟩ := hc.exists_fixedPoint' hs.isComplete hf (x := 0) (by intro i j; simp) (edist_ne_top _ _)
  refine ⟨Matrix.of y, hy, ?_⟩
  ext i j
  exact (congrFun (congrFun hfix i) j).symm

omit [IsUltrametricDist F] in
theorem prep_pow_sub_mulVec (p : ℕ) [Fact p.Prime] [CharP F p] (e n : ℕ) (A : Matrix m m F) (x : m → F) :
    (fun i => (x i ^ p ^ e - A.mulVec x i) ^ (p ^ e) ^ n) =
      (fun i => x i ^ (p ^ e) ^ (n + 1)) - (A.map (fun a => a ^ (p ^ e) ^ n)).mulVec (fun i => x i ^ (p ^ e) ^ n) := by
  funext i
  have hq : (p ^ e) ^ n = p ^ (e * n) := (pow_mul p e n).symm
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [pow_succ' (p ^ e) n, pow_mul (x i), hq, sub_pow_char_pow, sum_pow_char_pow]
  simp only [mul_pow]

omit [IsUltrametricDist F] in
theorem prep_identity (p : ℕ) [Fact p.Prime] [CharP F p] (e D : ℕ) (M U : ℕ → Matrix m m F) (A : Matrix m m F)
    (hD : U D = 0) (hU : ∀ n, n < D → U n = M (n + 1) + U (n + 1) * A.map (fun a => a ^ (p ^ e) ^ (n + 1)))
    (h0 : M 0 = -(U 0 * A)) (x : m → F) :
    gsum (p ^ e) D M x = gsum (p ^ e) D U (fun i => x i ^ p ^ e - A.mulVec x i) := by
  unfold gsum
  simp only [prep_pow_sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, sum_sub_distrib]
  rw [sum_range_succ', sum_range_succ, sum_range_succ', hD, h0]
  have : ∑ n ∈ range D, (U n).mulVec (fun i => x i ^ (p ^ e) ^ (n + 1)) =
      ∑ n ∈ range D, (M (n + 1)).mulVec (fun i => x i ^ (p ^ e) ^ (n + 1)) +
      ∑ n ∈ range D, (U (n + 1) * A.map (fun a => a ^ (p ^ e) ^ (n + 1))).mulVec
        (fun i => x i ^ (p ^ e) ^ (n + 1)) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [← Matrix.add_mulVec, ← hU n (mem_range.1 hn)]
  rw [this]
  have hA : A.map (fun a => a ^ (p ^ e) ^ 0) = A := by ext i j; simp
  rw [hA, Matrix.neg_mulVec, Matrix.zero_mulVec]
  abel

end Prep

theorem preparation : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (p : ℕ)
    [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → 1 ≤ D →
    ∀ M : ℕ → Matrix m m F, Normal 1 M → ∃ (A : Matrix m m F) (U : ℕ → Matrix m m F), (∀ i j, ‖A i j‖ ≤ 1) ∧
      (∀ i j, ‖(U 0 - 1) i j‖ < 1) ∧ (∀ n, 1 ≤ n → ∀ i j, ‖U n i j‖ < 1) ∧ M 0 = -(U 0 * A) ∧
      ∀ x : m → F, gsum (p ^ e) D M x = gsum (p ^ e) D U (fun i => x i ^ p ^ e - A.mulVec x i) := by
  intro F _ _ _ p _ _ m _ _ e D _ hD M hM
  obtain ⟨δ, hδ, hδ1, hMδ⟩ : ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 ∧ ∀ n, 2 ≤ n → n ≤ D → PrepBd δ (M n) := by
    let S : Finset (ℕ × m × m) := Icc 2 D ×ˢ univ
    refine ⟨((S.sup fun t => ‖M t.1 t.2.1 t.2.2‖₊ : NNReal) : ℝ), NNReal.coe_nonneg _, ?_, ?_⟩
    · have : (S.sup fun t => ‖M t.1 t.2.1 t.2.2‖₊) < 1 := by
        rw [Finset.sup_lt_iff (by simp)]
        intro t ht
        have h2 : 2 ≤ t.1 := (mem_Icc.1 (mem_product.1 ht).1).1
        exact_mod_cast hM.small t.1 (by omega) t.2.1 t.2.2
      exact_mod_cast this
    · intro n h2 hn i j
      have : ‖M n i j‖₊ ≤ S.sup fun t => ‖M t.1 t.2.1 t.2.2‖₊ :=
        Finset.le_sup (f := fun t : ℕ × m × m => ‖M t.1 t.2.1 t.2.2‖₊) (b := (n, i, j))
          (mem_product.2 ⟨mem_Icc.2 ⟨h2, hn⟩, mem_univ _⟩)
      exact_mod_cast this
  obtain ⟨k, rfl⟩ : ∃ k, D = k + 1 := ⟨D - 1, by omega⟩
  have hW : ∀ A : Matrix m m F, PrepBd 1 A →
      PrepBd δ (prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1)) := fun A hA => by
    have := PrepBd.mul hδ zero_le_one (prepV_bd (q := p ^ e) hδ hMδ hA k 1 le_rfl (by omega))
      (hA.map_pow ((p ^ e) ^ 1))
    rwa [mul_one] at this
  obtain ⟨A, hA, hfix⟩ := prep_fixed hδ hδ1 (M 0) (hM.int 0)
    (fun A => prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1)) hW (by
      intro A B ε hε hA hB h
      have e1 : prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1) -
          prepV (p ^ e) M B k 1 * B.map (fun a => a ^ (p ^ e) ^ 1) =
          (prepV (p ^ e) M A k 1 - prepV (p ^ e) M B k 1) * A.map (fun a => a ^ (p ^ e) ^ 1) +
          prepV (p ^ e) M B k 1 * (A.map (fun a => a ^ (p ^ e) ^ 1) - B.map (fun a => a ^ (p ^ e) ^ 1)) := by
        rw [Matrix.sub_mul, Matrix.mul_sub]; abel
      rw [e1]
      refine PrepBd.add ?_ ?_
      · have := PrepBd.mul (mul_nonneg hδ hε) zero_le_one
          (prepV_sub_bd p (e := e) hδ hε hMδ hA hB h k 1 le_rfl (by omega)) (hA.map_pow ((p ^ e) ^ 1))
        rwa [mul_one] at this
      · exact PrepBd.mul hδ hε (prepV_bd hδ hMδ hB k 1 le_rfl (by omega)) (PrepBd.map_pow_sub p e _ hA hB h))
  have hU0 : prepV (p ^ e) M A (k + 1 - 0) 0 = 1 + prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1) := by
    rw [Nat.sub_zero, prepV_succ, zero_add, hM.top]
  have h0 : M 0 = -(prepV (p ^ e) M A (k + 1 - 0) 0 * A) := by
    rw [hU0, Matrix.add_mul, Matrix.one_mul]
    have := eq_sub_iff_add_eq.1 hfix
    rw [this, neg_neg]
  refine ⟨A, fun n => prepV (p ^ e) M A (k + 1 - n) n, hA, ?_, ?_, h0, ?_⟩
  · intro i j
    beta_reduce
    rw [hU0, add_sub_cancel_left]
    exact (hW A hA i j).trans_lt hδ1
  · intro n hn i j
    beta_reduce
    by_cases h : n ≤ k + 1
    · exact (prepV_bd hδ hMδ hA _ n hn (by omega) i j).trans_lt hδ1
    · have : k + 1 - n = 0 := by omega
      simp [this, prepV_zero]
  · refine prep_identity p e (k + 1) M _ A (by simp [prepV_zero]) (fun n hn => ?_) h0
    have : k + 1 - n = (k + 1 - (n + 1)) + 1 := by omega
    beta_reduce
    rw [this, prepV_succ]

end GlobalTheory.PMonE

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AssociatedTraceAndLvlDvd
section
open PowerSeries GlobalTheory.CycFr

namespace GlobalTheory.CycFr.TraceOnePlusX

variable {l : ℕ} [Fact l.Prime]

theorem dvd_iff_toZMod (x : ℤ_[l]) : (l : ℤ_[l]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

theorem eq_one_of_pow_eq_one (hl : l ≠ 2) (x : ℤ_[l]) (n : ℕ) (hn : n ≠ 0) (hx : x ^ n = 1)
    (h1 : PadicInt.toZMod x = 1) : x = 1 := by
  have hp : l.Prime := Fact.out
  have hP : Prime (l : ℤ_[l]) := PadicInt.prime_p
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hp.ne_one
  have hd : (l : ℤ_[l]) ∣ x - 1 := by rw [dvd_iff_toZMod, map_sub, h1]; simp
  have hnd : ¬ (l : ℤ_[l]) ∣ x := by rw [dvd_iff_toZMod, h1]; simp
  have e1 := emultiplicity_pow_prime_pow_sub_pow_prime_pow hP (hp.odd_of_ne_two hl) hd hnd k
  have hd2 : (l : ℤ_[l]) ∣ x ^ l ^ k - 1 := by rw [dvd_iff_toZMod, map_sub, map_pow, h1]; simp
  have hnd2 : ¬ (l : ℤ_[l]) ∣ x ^ l ^ k := by rw [dvd_iff_toZMod, map_pow, h1]; simp
  have hm2 : ¬ (l : ℤ_[l]) ∣ (m : ℤ_[l]) := by
    rw [dvd_iff_toZMod, map_natCast, ZMod.natCast_eq_zero_iff]; exact hm
  have e2 := emultiplicity_pow_sub_pow_of_prime hP hd2 hnd2 hm2
  rw [← pow_mul, hx, one_pow, sub_self, emultiplicity_zero] at e2
  rw [one_pow, ← e2] at e1
  by_contra hne
  have hf : FiniteMultiplicity (l : ℤ_[l]) (x - 1) :=
    FiniteMultiplicity.of_prime_left hP (sub_ne_zero.2 hne)
  rw [hf.emultiplicity_eq_multiplicity] at e1
  exact absurd e1.symm (by exact_mod_cast ENat.coe_ne_top _)

theorem toZMod_unit_ne_zero (u : ℤ_[l]ˣ) : PadicInt.toZMod (u : ℤ_[l]) ≠ 0 :=
  (u.isUnit.map _).ne_zero

theorem unit_eq_one (hl : l ≠ 2) (u : ℤ_[l]ˣ) (hu : IsOfFinOrder u)
    (h1 : PadicInt.toZMod (u : ℤ_[l]) = 1) : u = 1 := by
  obtain ⟨n, hn, h⟩ := hu.exists_pow_eq_one
  apply Units.ext
  exact eq_one_of_pow_eq_one hl _ n hn.ne' (by rw [← Units.val_pow_eq_pow_val, h]; rfl) h1

theorem torsion_inj (hl : l ≠ 2) (u v : ℤ_[l]ˣ) (hu : IsOfFinOrder u) (hv : IsOfFinOrder v)
    (h : PadicInt.toZMod (u : ℤ_[l]) = PadicInt.toZMod (v : ℤ_[l])) : u = v := by
  have := unit_eq_one hl (u * v⁻¹) (hu.mul hv.inv) (by
    rw [Units.val_mul, map_mul, h, ← map_mul, ← Units.val_mul, mul_inv_cancel]; simp)
  exact mul_inv_eq_one.1 this

theorem pow_sub_one_eq_one (hl : l ≠ 2) (u : ℤ_[l]ˣ) (hu : IsOfFinOrder u) : u ^ (l - 1) = 1 :=
  unit_eq_one hl _ hu.pow (by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact ZMod.pow_card_sub_one_eq_one (toZMod_unit_ne_zero u))

theorem image_eq (D : Finset ℤ_[l]ˣ) (hl : l ≠ 2) (hc : D.card = l - 1)
    (hD : ∀ δ ∈ D, IsOfFinOrder δ) :
    D.image (fun δ : ℤ_[l]ˣ => PadicInt.toZMod (δ : ℤ_[l])) = Finset.univ.erase 0 := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨δ, -, rfl⟩ := Finset.mem_image.1 hx
    simp [toZMod_unit_ne_zero]
  · rw [Finset.card_image_of_injOn (fun u hu v hv h => torsion_inj hl u v (hD u hu) (hD v hv) h),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card, hc]

theorem mem_of_torsion (D : Finset ℤ_[l]ˣ) (hl : l ≠ 2) (hc : D.card = l - 1)
    (hD : ∀ δ ∈ D, IsOfFinOrder δ) (u : ℤ_[l]ˣ) (hu : IsOfFinOrder u) : u ∈ D := by
  have : PadicInt.toZMod (u : ℤ_[l]) ∈
      D.image (fun δ : ℤ_[l]ˣ => PadicInt.toZMod (δ : ℤ_[l])) := by
    rw [image_eq D hl hc hD]; simp [toZMod_unit_ne_zero]
  obtain ⟨δ, hδ, h⟩ := Finset.mem_image.1 this
  rwa [← torsion_inj hl δ u (hD δ hδ) hu h]

theorem sum_pow_eq_zero (D : Finset ℤ_[l]ˣ) (hl : l ≠ 2) (hc : D.card = l - 1)
    (hD : ∀ δ ∈ D, IsOfFinOrder δ) (i : ℕ) (hi : i ≠ 0) (hi2 : i < l - 1) :
    ∑ δ ∈ D, (δ : ℤ_[l]) ^ i = 0 := by
  classical
  let G : Subgroup ℤ_[l]ˣ := CommGroup.torsion ℤ_[l]ˣ
  have hG : ∀ x, x ∈ D ↔ x ∈ G := fun x => ⟨hD x, mem_of_torsion D hl hc hD x⟩
  letI : Fintype G := Fintype.ofFinset D (fun x => hG x)
  have hcard : Fintype.card G = D.card := Fintype.card_of_subtype D hG
  rw [Finset.sum_subtype D hG (F := inferInstance) (fun δ : ℤ_[l]ˣ => (δ : ℤ_[l]) ^ i)]
  exact FiniteField.sum_subgroup_pow_eq_zero hi (by omega)

theorem sum_eval (D : Finset ℤ_[l]ˣ) (hl : l ≠ 2) (hc : D.card = l - 1)
    (hD : ∀ δ ∈ D, IsOfFinOrder δ) (P : Polynomial ℤ_[l]) (hP : P.natDegree < l)
    (h0 : P.coeff 0 = 0) :
    ∑ δ ∈ D, P.eval (δ : ℤ_[l]) = ((l - 1 : ℕ) : ℤ_[l]) * P.coeff (l - 1) := by
  have hp : l.Prime := Fact.out
  have := hp.two_le
  simp_rw [Polynomial.eval_eq_sum_range' hP]
  rw [Finset.sum_comm, Finset.sum_eq_single (l - 1)]
  · rw [← Finset.mul_sum, mul_comm, Finset.sum_congr rfl (g := fun _ => (1 : ℤ_[l]))]
    · simp [hc]
    · intro δ hδ
      rw [← Units.val_pow_eq_pow_val, pow_sub_one_eq_one hl δ (hD δ hδ)]; rfl
  · intro i hi hne
    rw [← Finset.mul_sum]
    by_cases hi0 : i = 0
    · rw [hi0, h0, zero_mul]
    · rw [sum_pow_eq_zero D hl hc hD i hi0 (by have := Finset.mem_range.1 hi; omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem factorial_mul_choose (c : ℤ_[l]) (k : ℕ) :
    (k.factorial : ℤ_[l]) * Ring.choose c k = (descPochhammer ℤ_[l] k).eval c := by
  rw [← nsmul_eq_mul, ← Ring.descPochhammer_eq_factorial_smul_choose, ← Polynomial.aeval_eq_smeval,
    ← descPochhammer_map (algebraMap ℤ ℤ_[l]), Polynomial.eval_map_algebraMap]

theorem factorial_mul_sum_choose (D : Finset ℤ_[l]ˣ) (hl : l ≠ 2) (hc : D.card = l - 1)
    (hD : ∀ δ ∈ D, IsOfFinOrder δ) (k : ℕ) (hk : k ≠ 0) (hk2 : k < l) :
    (k.factorial : ℤ_[l]) * ∑ δ ∈ D, Ring.choose (δ : ℤ_[l]) k =
      ((l - 1 : ℕ) : ℤ_[l]) * (descPochhammer ℤ_[l] k).coeff (l - 1) := by
  rw [Finset.mul_sum]
  simp_rw [factorial_mul_choose]
  apply sum_eval D hl hc hD
  · rwa [descPochhammer_natDegree]
  · rw [Polynomial.coeff_zero_eq_eval_zero]; exact descPochhammer_ne_zero_eval_zero _ hk

theorem sum_choose_eq_zero (D : Finset ℤ_[l]ˣ) (hl : l ≠ 2) (hc : D.card = l - 1)
    (hD : ∀ δ ∈ D, IsOfFinOrder δ) (k : ℕ) (hk : k ≠ 0) (hk2 : k < l - 1) :
    ∑ δ ∈ D, Ring.choose (δ : ℤ_[l]) k = 0 := by
  have h := factorial_mul_sum_choose D hl hc hD k hk (by omega)
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [descPochhammer_natDegree]), mul_zero] at h
  exact (mul_eq_zero.1 h).resolve_left (by exact_mod_cast k.factorial_ne_zero)

theorem isUnit_sum_choose (D : Finset ℤ_[l]ˣ) (hl : l ≠ 2) (hc : D.card = l - 1)
    (hD : ∀ δ ∈ D, IsOfFinOrder δ) : IsUnit (∑ δ ∈ D, Ring.choose (δ : ℤ_[l]) (l - 1)) := by
  have hp : l.Prime := Fact.out
  have := hp.two_le
  have h := factorial_mul_sum_choose D hl hc hD (l - 1) (by omega) (by omega)
  have hm : (descPochhammer ℤ_[l] (l - 1)).coeff (l - 1) = 1 := by
    have := (monic_descPochhammer ℤ_[l] (l - 1)).coeff_natDegree
    rwa [descPochhammer_natDegree] at this
  rw [hm, mul_one] at h
  have hu : IsUnit ((l - 1 : ℕ) : ℤ_[l]) := by
    by_contra hn
    have : ((l - 1 : ℕ) : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := hn
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by omega) this
    omega
  rw [← h] at hu
  exact isUnit_of_mul_isUnit_right hu

end GlobalTheory.CycFr.TraceOnePlusX

namespace GlobalTheory.CycFr

open TraceOnePlusX

theorem associated_trace_and_lvl_dvd {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [CharZero O] [Algebra ℤ_[l] O] (D : Finset ℤ_[l]ˣ) (hl : l ≠ 2) (hc : D.card = l - 1)
    (hD : ∀ δ ∈ D, IsOfFinOrder δ) :
    Associated (1 - (l : O⟦X⟧) + ∑ δ ∈ D, act O (δ : ℤ_[l]) (1 + X)) (X ^ (l - 1)) ∧
      lvl l O 0 ∣ 1 + ∑ δ ∈ D, act O (δ : ℤ_[l]) (1 + X) := by
  have hp : l.Prime := Fact.out
  have h2 := hp.two_le
  simp_rw [act_one_add_X]
  constructor
  · have hco : ∀ k, k ≠ 0 → coeff k (1 - (l : O⟦X⟧) + ∑ δ ∈ D, bin O (δ : ℤ_[l])) =
        algebraMap ℤ_[l] O (∑ δ ∈ D, Ring.choose (δ : ℤ_[l]) k) := by
      intro k hk
      have e : (1 - (l : O⟦X⟧)) = C (1 - (l : O)) := by simp
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e, map_add (f := _), coeff_C, if_neg hk, zero_add, map_sum, map_sum]
      refine Finset.sum_congr rfl fun δ _ => ?_
      rw [binomialSeries_coeff, Algebra.smul_def, mul_one]
    obtain ⟨g, hg⟩ : (X : O⟦X⟧) ^ (l - 1) ∣ 1 - (l : O⟦X⟧) + ∑ δ ∈ D, bin O (δ : ℤ_[l]) := by
      rw [X_pow_dvd_iff]
      intro m hm
      by_cases h0 : m = 0
      · subst h0
        simp [bin, binomialSeries_constantCoeff, hc, Nat.cast_sub hp.one_le]
      · rw [hco m h0, sum_choose_eq_zero D hl hc hD m h0 hm, map_zero]
    have hu : IsUnit g := by
      rw [PowerSeries.isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply,
        ← coeff_X_pow_mul g (l - 1) 0, ← hg, zero_add, hco _ (by omega)]
      exact (isUnit_sum_choose D hl hc hD).map _
    rw [hg]
    exact associated_mul_unit_left _ _ hu
  · have hq : lvl l O 0 ∣ (1 + X : O⟦X⟧) ^ l ^ 1 - 1 := Dvd.intro_left _ (mul_lvl 0)
    have h1 : lvl l O 0 ∣ ∑ δ ∈ D, (bin O (δ : ℤ_[l]) -
        (1 + X) ^ (PadicInt.toZMod (δ : ℤ_[l])).val) := by
      refine Finset.dvd_sum fun δ _ => hq.trans ?_
      rw [← bin_nat (l := l) (PadicInt.toZMod (δ : ℤ_[l])).val]
      apply dvd_bin_sub
      rw [pow_one, dvd_iff_toZMod, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    have h3 : 1 + ∑ δ ∈ D, (1 + X : O⟦X⟧) ^ (PadicInt.toZMod (δ : ℤ_[l])).val = lvl l O 0 := by
      rw [← Finset.sum_image (s := D) (g := fun δ : ℤ_[l]ˣ => PadicInt.toZMod (δ : ℤ_[l]))
        (f := fun x : ZMod l => (1 + X : O⟦X⟧) ^ x.val)
        (fun u hu v hv h => torsion_inj hl u v (hD u hu) (hD v hv) h), image_eq D hl hc hD]
      have := Finset.add_sum_erase Finset.univ (fun x : ZMod l => (1 + X : O⟦X⟧) ^ x.val)
        (Finset.mem_univ 0)
      simp only [ZMod.val_zero, pow_zero] at this
      rw [this, lvl]
      simp only [pow_zero, pow_one]
      refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
      · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
      · intro x _ y _ h; exact ZMod.val_injective l h
      · intro i hi; exact ⟨(i : ZMod l), Finset.mem_univ _, ZMod.val_cast_of_lt (Finset.mem_range.1 hi)⟩
      · intro x _; rfl
    rw [Finset.sum_sub_distrib] at h1
    have := dvd_add h1 (dvd_refl _)
    convert this using 1
    rw [← h3]; ring

end GlobalTheory.CycFr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EchelonProjectorKernelFrobeniusStatement
section
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.echelon_projector_kernel_frobenius : ∀ (l : ℕ) [Fact l.Prime] (C : Type) [Field C] [CharP C l] (d : ℕ) (Y A : Matrix (Fin d) (Fin d) C), A.det ≠ 0 → Y.map (frobenius C l) = Y * A → ∃ (I : Finset (Fin d)) (Q Λ : Matrix (Fin d) (Fin d) C), Y * Q = 0 ∧ (∀ v, Y.mulVec v = 0 → Q.mulVec v = v) ∧ (∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0) ∧ (∀ i, ∀ j ∉ I, Q i j = 0) ∧ Q = A * Q.map (frobenius C l) * Λ := by
  first | exact @GlobalTheory.echelon_projector_frobenius | exact GlobalTheory.echelon_projector_frobenius | (intros; apply GlobalTheory.echelon_projector_frobenius <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfRootCongrOfDerivUnitStatement
section
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_roots_congr_of_derivative_unit : ∀ {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (f : Polynomial ℤ) (β β' : Ω),
    A.valuation β ≤ 1 → A.valuation β' ≤ 1 → Polynomial.aeval β f = 0 → Polynomial.aeval β' f = 0 →
    ¬ A.valuation (Polynomial.aeval β (Polynomial.derivative f)) < 1 → A.valuation (β - β') < 1 → β = β' := by
  first | exact @GlobalTheory.eq_of_root_congr_of_deriv_unit | exact GlobalTheory.eq_of_root_congr_of_deriv_unit | (intros; apply GlobalTheory.eq_of_root_congr_of_deriv_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfSumMulEmbeddingsEqZeroStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_sum_mul_embeddings_eq_zero' : ∀ (F Ω L : Type) [Field F] [CharZero F] [Field Ω] [IsAlgClosed Ω] [Algebra F Ω] [Field L] [Algebra F L] [FiniteDimensional F L] (m : ℕ) (e : Fin m → Ω), LinearIndependent F e → (∀ t, IsAlgebraic F (e t)) → ∀ a : Fin m → L, (∀ σ : L →ₐ[F] Ω, ∑ t, e t * σ (a t) = 0) → a = 0 := by
  first | exact @GlobalTheory.eq_zero_of_sum_mul_embeddings_eq_zero | exact GlobalTheory.eq_zero_of_sum_mul_embeddings_eq_zero | (intros; apply GlobalTheory.eq_zero_of_sum_mul_embeddings_eq_zero <;> assumption)
end

