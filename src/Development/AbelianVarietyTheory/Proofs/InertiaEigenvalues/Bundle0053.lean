module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IwahoriFactorisation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetSuccEqSubSumUpdateRow
section
namespace GlobalTheory.PsChar

open Matrix

theorem det_succ_eq_sub_sum_updateRow {A : Type*} [CommRing A] {m : ℕ} (N : Matrix (Fin (m + 1)) (Fin (m + 1)) A) :
    N.det = N 0 0 * (N.submatrix Fin.succ Fin.succ).det -
      ∑ c : Fin m, N c.succ 0 * ((N.submatrix Fin.succ Fin.succ).updateRow c (fun b => N 0 b.succ)).det := by
  rw [Matrix.det_apply', Finset.univ_perm_fin_succ, Finset.sum_map, Fintype.sum_prod_type, Fin.sum_univ_succ,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · rw [Matrix.det_apply', Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp [Fin.prod_univ_succ, Equiv.Perm.decomposeFin.symm_sign]
    ring
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.det_apply', Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h : ∀ i : Fin m, N (Equiv.swap 0 c.succ (e i).succ) i.succ =
        (N.submatrix Fin.succ Fin.succ).updateRow c (fun b => N 0 b.succ) (e i) i := by
      intro i
      by_cases hc : e i = c
      · simp [hc]
      · rw [Matrix.updateRow_ne hc, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
          (fun h => hc (Fin.succ_injective _ h))]
        rfl
    simp [Fin.prod_univ_succ, Equiv.Perm.decomposeFin.symm_sign, h]
    ring

theorem alt_trace_eq_sum_det {M A : Type*} [Monoid M] [CommRing A] {n : ℕ} (r : M →* Matrix (Fin n) (Fin n) A) :
    ∀ (m : ℕ) (x : Fin m → M), alt (fun g => (r g).trace) m x =
      ∑ i : Fin m → Fin n, (Matrix.of fun a b => r (x a) (i b) (i a)).det
  | 0, x => by simp [alt]
  | m + 1, x => by
    rw [alt, ← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin n)).sum_comp, Fintype.sum_prod_type]
    simp only [alt_trace_eq_sum_det r m, det_succ_eq_sub_sum_updateRow, Finset.sum_sub_distrib]
    congr 1
    · rw [Matrix.trace, Finset.sum_mul_sum]
      rfl
    · rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h1 : (Matrix.of fun a b => r (Function.update (Fin.tail x) c (x 0 * Fin.tail x c) a) (i b) (i a)) =
          (Matrix.of fun a b => r (x a.succ) (i b) (i a)).updateRow c
            (∑ j : Fin n, r (x c.succ) j (i c) • fun b => r (x 0) (i b) j) := by
        ext a b
        by_cases h : a = c
        · subst h
          simp [Fin.tail, Matrix.mul_apply, mul_comm]
        · simp [Fin.tail, h]
      rw [h1]
      have h2 : ∀ (P : Matrix (Fin m) (Fin m) A) (s : Finset (Fin n)) (w : Fin n → A) (v : Fin n → Fin m → A),
          (P.updateRow c (∑ j ∈ s, w j • v j)).det = ∑ j ∈ s, w j * (P.updateRow c (v j)).det := by
        intro P s w v
        induction s using Finset.induction_on with
        | empty =>
          simp only [Finset.sum_empty]
          exact Matrix.det_eq_zero_of_row_eq_zero c (by simp)
        | insert j s hj ih =>
          rw [Finset.sum_insert hj, Finset.sum_insert hj, Matrix.det_updateRow_add, ih, Matrix.det_updateRow_smul]
      rw [h2]
      rfl

theorem isPsChar_trace (M A : Type) [Monoid M] [CommRing A] (n : ℕ) (r : M →* Matrix (Fin n) (Fin n) A) :
    IsPsChar n (fun g => (r g).trace) := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro x y
    simp only [map_mul]
    exact Matrix.trace_mul_comm _ _
  · intro x
    rw [alt_trace_eq_sum_det]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨b, b', hne, hb⟩ := Fintype.exists_ne_map_eq_of_card_lt i (by simp)
    exact Matrix.det_zero_of_column_eq hne (fun a => by simp [hb])

end GlobalTheory.PsChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedDifferenceIdealPowerMem
section
open Polynomial

namespace GlobalTheory.FilCoeff

theorem poly_eq_zero_of_eval_nat {R : Type} [CommRing R]
    (hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) :
    ∀ (n : ℕ) (F : R[X]), F.natDegree ≤ n → ∀ m : ℕ,
      (∀ k : ℕ, F.eval ((m + k : ℕ) : R) = 0) → F = 0 := by
  first
  | exact @_root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add
  | exact _root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add
  | (apply _root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add ..)

noncomputable def binPoly {R : Type} [CommRing R] (y : R) (s : ℕ) : R[X] :=
  ∑ j ∈ Finset.range s, C (y ^ j * Ring.inverse ((j.factorial : ℕ) : R)) * descPochhammer R j

theorem eval_binPoly {R : Type} [CommRing R] (hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R))
    (y : R) (s : ℕ) (hy : y ^ s = 0) (k : ℕ) :
    (binPoly y s).eval ((k : ℕ) : R) = (1 + y) ^ k := by
  have hterm : ∀ j ∈ Finset.range s,
      eval ((k : ℕ) : R) (C (y ^ j * Ring.inverse ((j.factorial : ℕ) : R)) * descPochhammer R j)
        = y ^ j * ((k.choose j : ℕ) : R) := by
    intro j _
    rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, mul_assoc, ← mul_assoc (Ring.inverse _),
      Ring.inverse_mul_cancel _ (hR _ (Nat.factorial_ne_zero j)), one_mul]
  rw [binPoly, eval_finsetSum, Finset.sum_congr rfl hterm, add_comm, add_pow]
  simp only [one_pow, mul_one]
  have h1 : ∑ j ∈ Finset.range s, y ^ j * ((k.choose j : ℕ) : R)
      = ∑ j ∈ Finset.range (s + k + 1), y ^ j * ((k.choose j : ℕ) : R) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    rw [Finset.mem_range, not_lt] at hj
    rw [pow_eq_zero_of_le hj hy, zero_mul]
  have h2 : ∑ j ∈ Finset.range (k + 1), y ^ j * ((k.choose j : ℕ) : R)
      = ∑ j ∈ Finset.range (s + k + 1), y ^ j * ((k.choose j : ℕ) : R) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    rw [Finset.mem_range, not_lt] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
  rw [h1, h2]

theorem smul_coeff_one_eq_zero {R : Type} [CommRing R] (hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R))
    (y : R) (s : ℕ) (hy : y ^ s = 0) (c : ℕ → R)
    (h : ∀ k : ℕ, ∑ i ∈ Finset.range s, ((1 + y) ^ k - 1) ^ i * c i = 0) :
    y * c 1 = 0 := by
  rcases s with _ | _ | t
  · have h1 : (1 : R) = 0 := by simpa using hy
    calc y * c 1 = y * c 1 * 1 := (mul_one _).symm
      _ = 0 := by rw [h1, mul_zero]
  · rw [zero_add, pow_one] at hy; rw [hy, zero_mul]
  set P : R[X] := binPoly y (t + 2) - 1 with hPdef
  have hP : ∀ k : ℕ, P.eval ((k : ℕ) : R) = (1 + y) ^ k - 1 := by
    intro k; rw [hPdef, eval_sub, eval_one, eval_binPoly hR y _ hy k]
  set F : R[X] := ∑ i ∈ Finset.range (t + 2), P ^ i * C (c i) with hFdef
  have hF : F = 0 := by
    apply poly_eq_zero_of_eval_nat hR F.natDegree F le_rfl 0
    intro k
    rw [zero_add, hFdef, eval_finsetSum]
    simp only [eval_mul, eval_pow, eval_C, hP]
    exact h k
  have h0 : P.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]; simpa using hP 0
  obtain ⟨Q, hQ⟩ := X_dvd_iff.2 h0
  have hF1 : F.coeff 1 = Q.coeff 0 * c 1 := by
    rw [hFdef, finsetSum_coeff]
    simp only [coeff_mul_C, hQ, mul_pow, coeff_X_pow_mul']
    rw [Finset.sum_eq_single 1]
    · simp
    · intro i _ hi
      rcases Nat.lt_or_gt_of_ne hi with hi | hi
      · have : i = 0 := by omega
        subst this; simp [coeff_one]
      · rw [if_neg (by omega), zero_mul]
    · intro hn; exact absurd (Finset.mem_range.2 (by omega)) hn
  have hL : P.coeff 1 = Q.coeff 0 := by rw [hQ, coeff_X_mul]
  have hL2 : P.coeff 1 = y * (1 + (∑ j ∈ Finset.range t, y ^ j *
      Ring.inverse (((j + 2).factorial : ℕ) : R) * (descPochhammer R (j + 2)).coeff 1) * y) := by
    rw [hPdef, coeff_sub, coeff_one, if_neg one_ne_zero, sub_zero, binPoly, finsetSum_coeff]
    simp only [coeff_C_mul]
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [zero_add, pow_one, pow_zero, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
      Ring.inverse_one, descPochhammer_one, descPochhammer_zero, coeff_X_one, coeff_one,
      if_neg one_ne_zero, mul_zero, add_zero, mul_one, one_mul]
    have e : ∀ j ∈ Finset.range t, y ^ (j + 1 + 1) * Ring.inverse (((j + 1 + 1).factorial : ℕ) : R)
        * (descPochhammer R (j + 1 + 1)).coeff 1
        = y * ((y ^ j * Ring.inverse (((j + 2).factorial : ℕ) : R) * (descPochhammer R (j + 2)).coeff 1) * y) := by
      intro j _; ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hnil : IsNilpotent ((∑ j ∈ Finset.range t, y ^ j *
      Ring.inverse (((j + 2).factorial : ℕ) : R) * (descPochhammer R (j + 2)).coeff 1) * y) :=
    (Commute.all _ y).isNilpotent_mul_left ⟨_, hy⟩
  have hc := congrArg (fun G : R[X] => G.coeff 1) hF
  simp only [hF1, coeff_zero] at hc
  rw [← hL, hL2, mul_comm, ← mul_assoc, mul_comm (c 1), mul_comm _ (1 + _)] at hc
  have := (hnil.isUnit_one_add).mul_right_eq_zero.1 hc
  rw [mul_comm] at this ⊢; exact (mul_comm (c 1) y) ▸ this

theorem d_mul_x_one_mem_span_pow :
    ∀ (B : Type) [CommRing B], (∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) → ∀ (d q u : B), IsUnit u →
      q - 1 = d * u → ∀ (s : ℕ) (x : ℕ → B),
      (∀ k : ℕ, ∑ i ∈ Finset.range s, (q ^ k - 1) ^ i * Ring.inverse (i.factorial : B) * x i
        ∈ Ideal.span {d ^ s}) → d * x 1 ∈ Ideal.span {d ^ s} := by
  intro B _ hB d q u hu hq s x hx
  set I : Ideal B := Ideal.span {d ^ s} with hI
  have hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B ⧸ I) := fun n hn => by
    simpa using (hB n hn).map (Ideal.Quotient.mk I)
  have hy : (Ideal.Quotient.mk I q - 1) ^ s = 0 := by
    rw [← map_one (Ideal.Quotient.mk I), ← map_sub, hq, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
      mul_pow]
    exact I.mul_mem_right _ (Ideal.subset_span rfl)
  have key := smul_coeff_one_eq_zero hR (Ideal.Quotient.mk I q - 1) s hy
    (fun i => Ideal.Quotient.mk I (Ring.inverse (i.factorial : B) * x i)) (by
      intro k
      rw [add_sub_cancel]
      have := (Ideal.Quotient.eq_zero_iff_mem).2 (hx k)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      simpa only [map_mul, map_pow, map_sub, map_one, mul_assoc] using this)
  simp only [Nat.factorial_one, Nat.cast_one, Ring.inverse_one, one_mul] at key
  rw [← map_one (Ideal.Quotient.mk I), ← map_sub, hq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at key
  obtain ⟨v, rfl⟩ := hu
  have : d * x 1 = d * ↑v * x 1 * ↑v⁻¹ := by
    rw [mul_right_comm d, mul_assoc, mul_assoc, Units.mul_inv, mul_one]
  rw [this]
  exact I.mul_mem_right _ key

end GlobalTheory.FilCoeff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdInvOfBlockTriangular
section
open Polynomial

namespace GlobalTheory.IwahoriFactor

section General

variable {O : Type} [CommRing O] {n : ℕ}

def Shape (α β : O) (g : Matrix (Fin n) (Fin n) O) : Prop :=
  ∀ i j, (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)

def UpperUnip (α : O) (u : Matrix (Fin n) (Fin n) O) : Prop :=
  ∀ i j, (j < i → u i j = 0) ∧ (i = j → u i j = 1) ∧ (i < j → α ∣ u i j)

def LowerUnip (β : O) (l : Matrix (Fin n) (Fin n) O) : Prop :=
  ∀ i j, (i < j → l i j = 0) ∧ (i = j → l i j = 1) ∧ (j < i → β ∣ l i j)

theorem Shape.mul {α β : O} {x y : Matrix (Fin n) (Fin n) O} (hx : Shape α β x)
    (hy : Shape α β y) : Shape α β (x * y) := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.dvd_sum fun k _ => ?_
    rcases lt_or_ge i k with hk | hk
    · exact ((hx i k).1 hk).mul_right _
    · exact ((hy k j).1 (hk.trans_lt h)).mul_left _
  · rw [Matrix.mul_apply]
    refine Finset.dvd_sum fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · exact ((hx i k).2 hk).mul_right _
    · exact ((hy k j).2 (h.trans_le hk)).mul_left _

theorem dvd_inv_of_blockTriangular {ι : Type} [LinearOrder ι] (b : Fin n → ι) (γ : O)
    (g : GL (Fin n) O) (hg : ∀ i j, b j < b i → γ ∣ (g : Matrix (Fin n) (Fin n) O) i j) :
    ∀ i j, b j < b i → γ ∣ ((g⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) i j := by
  let f := Ideal.Quotient.mk (Ideal.span {γ})
  have hf : ∀ x, f x = 0 ↔ γ ∣ x := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have h1 : ((g : Matrix (Fin n) (Fin n) O).map f) *
      (((g⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O).map f) = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero f) (map_one f)]
  letI := invertibleOfRightInverse _ _ h1
  have h2 : ((g : Matrix (Fin n) (Fin n) O).map f).BlockTriangular b :=
    fun i j h => (hf _).2 (hg i j h)
  have h3 := Matrix.blockTriangular_inv_of_blockTriangular h2
  rw [Matrix.inv_eq_right_inv h1] at h3
  intro i j h
  exact (hf _).1 (h3 h)

theorem Shape.inv {α β : O} {g : GL (Fin n) O} (hg : Shape α β (g : Matrix (Fin n) (Fin n) O)) :
    Shape α β ((g⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact dvd_inv_of_blockTriangular (ι := (Fin n)ᵒᵈ) OrderDual.toDual α g
      (fun i j h => (hg i j).1 h) i j h
  · exact dvd_inv_of_blockTriangular id β g (fun i j h => (hg i j).2 h) i j h

theorem UpperUnip.shape {α : O} (β : O) {u : Matrix (Fin n) (Fin n) O} (hu : UpperUnip α u) :
    Shape α β u := fun i j =>
  ⟨(hu i j).2.2, fun h => by rw [(hu i j).1 h]; exact dvd_zero _⟩

theorem LowerUnip.shape (α : O) {β : O} {l : Matrix (Fin n) (Fin n) O} (hl : LowerUnip β l) :
    Shape α β l := fun i j =>
  ⟨fun h => by rw [(hl i j).1 h]; exact dvd_zero _, (hl i j).2.2⟩

theorem Shape.diagonal (α β : O) (d : Fin n → O) : Shape α β (Matrix.diagonal d) := fun i j =>
  ⟨fun h => by rw [Matrix.diagonal_apply_ne _ h.ne]; exact dvd_zero _,
    fun h => by rw [Matrix.diagonal_apply_ne _ h.ne']; exact dvd_zero _⟩

theorem UpperUnip.det {α : O} {u : Matrix (Fin n) (Fin n) O} (hu : UpperUnip α u) :
    u.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j h => (hu i j).1 h)]
  exact Finset.prod_eq_one fun i _ => (hu i i).2.1 rfl

theorem LowerUnip.det {β : O} {l : Matrix (Fin n) (Fin n) O} (hl : LowerUnip β l) :
    l.det = 1 := by
  rw [Matrix.det_of_lowerTriangular l (fun i j h => (hl i j).1 h)]
  exact Finset.prod_eq_one fun i _ => (hl i i).2.1 rfl

theorem factor_unique {α β α' β' : O} {u u' l l' : Matrix (Fin n) (Fin n) O} {d d' : Fin n → Oˣ}
    (hu : UpperUnip α u) (hu' : UpperUnip α' u') (hl : LowerUnip β l) (hl' : LowerUnip β' l')
    (h : u * Matrix.diagonal (fun i => (d i : O)) * l =
      u' * Matrix.diagonal (fun i => (d' i : O)) * l') :
    u = u' ∧ d = d' ∧ l = l' := by
  have iu' : IsUnit u'.det := by rw [hu'.det]; exact isUnit_one
  have il : IsUnit l.det := by rw [hl.det]; exact isUnit_one
  letI := u'.invertibleOfIsUnitDet iu'
  letI := l.invertibleOfIsUnitDet il
  have tu : u.BlockTriangular id := fun i j h => (hu i j).1 h
  have tu' : u'.BlockTriangular id := fun i j h => (hu' i j).1 h
  have tl : l.BlockTriangular OrderDual.toDual := fun i j h => (hl i j).1 h
  have tl' : l'.BlockTriangular OrderDual.toDual := fun i j h => (hl' i j).1 h
  set X := u'⁻¹ * (u * Matrix.diagonal (fun i => (d i : O))) with hX
  have e1 : u' * X = u * Matrix.diagonal (fun i => (d i : O)) := by
    rw [hX, Matrix.mul_nonsing_inv_cancel_left _ _ iu']
  have e2 : X * l = Matrix.diagonal (fun i => (d' i : O)) * l' := by
    rw [hX, Matrix.mul_assoc, h, Matrix.mul_assoc u', Matrix.nonsing_inv_mul_cancel_left _ _ iu']
  have e3 : X = Matrix.diagonal (fun i => (d' i : O)) * l' * l⁻¹ := by
    rw [← e2, Matrix.mul_nonsing_inv_cancel_right _ _ il]
  have tX : X.BlockTriangular id :=
    (Matrix.blockTriangular_inv_of_blockTriangular tu').mul
      (tu.mul (Matrix.blockTriangular_diagonal _))
  have tX' : X.BlockTriangular OrderDual.toDual := by
    rw [e3]
    exact ((Matrix.blockTriangular_diagonal _).mul tl').mul
      (Matrix.blockTriangular_inv_of_blockTriangular tl)
  have hd : X = Matrix.diagonal (fun i => X i i) := by
    ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [Matrix.diagonal_apply_ne _ h.ne]; exact tX' h
    · rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h.ne']; exact tX h
  rw [hd] at e1 e2
  have f1 : ∀ i j, u' i j * X j j = u i j * d j := fun i j => by
    simpa [Matrix.mul_diagonal] using congrFun (congrFun e1 i) j
  have f2 : ∀ i j, X i i * l i j = d' i * l' i j := fun i j => by
    simpa [Matrix.diagonal_mul] using congrFun (congrFun e2 i) j
  have g1 : ∀ i, X i i = d i := fun i => by
    simpa [(hu i i).2.1 rfl, (hu' i i).2.1 rfl] using f1 i i
  have g2 : ∀ i, X i i = d' i := fun i => by
    simpa [(hl i i).2.1 rfl, (hl' i i).2.1 rfl] using f2 i i
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have := f1 i j
    rw [g1] at this
    exact ((Units.mul_left_inj _).1 this).symm
  · funext i
    exact Units.ext ((g1 i).symm.trans (g2 i))
  · ext i j
    have := f2 i j
    rw [g2] at this
    exact (Units.mul_right_inj _).1 this

theorem exists_factor [IsLocalRing O] {α β : O} (hαβ : ¬ IsUnit (α * β)) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), Shape α β g → (∀ i, IsUnit (g i i)) →
      ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O),
        UpperUnip α u ∧ LowerUnip β l ∧ g = u * Matrix.diagonal (fun i => (d i : O)) * l ∧
          ∀ i, α * β ∣ (d i : O) - g i i := by
  first
  | exact @_root_.GlobalTheory.UnipotentDecomposition.main
  | exact _root_.GlobalTheory.UnipotentDecomposition.main
  | (apply _root_.GlobalTheory.UnipotentDecomposition.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnipotentDecomposition.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnipotentDecomposition.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnipotentDecomposition.main ..)

theorem isUnit_diag [IsLocalRing O] {α β : O} (hβ : ¬ IsUnit β) {g : Matrix (Fin n) (Fin n) O}
    (hdet : IsUnit g.det) (hg : Shape α β g) (i : Fin n) : IsUnit (g i i) := by
  let f := IsLocalRing.residue O
  have h0 : ∀ x, f x = 0 ↔ ¬ IsUnit x := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have h1 : (g.map f).BlockTriangular id := fun i j h =>
    (h0 _).2 fun hu => hβ (isUnit_of_dvd_unit ((hg i j).2 h) hu)
  have h2 : f g.det = ∏ k, f (g k k) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.det_of_upperTriangular h1]
    rfl
  by_contra hi
  have h3 : f g.det = 0 := by
    rw [h2]; exact Finset.prod_eq_zero (Finset.mem_univ i) ((h0 _).2 hi)
  exact (h0 _).1 h3 hdet

def flip (g : Matrix (Fin n) (Fin n) O) : Matrix (Fin n) (Fin n) O :=
  g.submatrix Fin.revPerm Fin.revPerm

theorem flip_apply (g : Matrix (Fin n) (Fin n) O) (i j : Fin n) :
    flip g i j = g i.rev j.rev := rfl

theorem flip_flip (g : Matrix (Fin n) (Fin n) O) : flip (flip g) = g := by
  ext i j; simp [flip_apply]

theorem flip_triple (u l : Matrix (Fin n) (Fin n) O) (d : Fin n → O) :
    flip (u * Matrix.diagonal d * l) =
      flip u * Matrix.diagonal (fun i => d i.rev) * flip l := by
  unfold flip
  rw [← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm, ← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm,
    Matrix.submatrix_diagonal_equiv]
  rfl

theorem Shape.flip {α β : O} {g : Matrix (Fin n) (Fin n) O} (hg : Shape α β g) :
    Shape β α (flip g) := fun i j =>
  ⟨fun h => (hg _ _).2 (Fin.rev_lt_rev.2 h), fun h => (hg _ _).1 (Fin.rev_lt_rev.2 h)⟩

theorem UpperUnip.flip {α : O} {u : Matrix (Fin n) (Fin n) O} (hu : UpperUnip α u) :
    LowerUnip α (flip u) := fun i j =>
  ⟨fun h => (hu _ _).1 (Fin.rev_lt_rev.2 h), fun h => (hu _ _).2.1 (congrArg Fin.rev h),
    fun h => (hu _ _).2.2 (Fin.rev_lt_rev.2 h)⟩

theorem LowerUnip.flip {β : O} {l : Matrix (Fin n) (Fin n) O} (hl : LowerUnip β l) :
    UpperUnip β (flip l) := fun i j =>
  ⟨fun h => (hl _ _).1 (Fin.rev_lt_rev.2 h), fun h => (hl _ _).2.1 (congrArg Fin.rev h),
    fun h => (hl _ _).2.2 (Fin.rev_lt_rev.2 h)⟩

theorem not_isUnit_mul {α β : O} (hβ : ¬ IsUnit β) : ¬ IsUnit (α * β) :=
  fun h => hβ (isUnit_of_mul_isUnit_right h)

theorem existsUnique_factor [IsLocalRing O] {α β : O} (hβ : ¬ IsUnit β) (g : GL (Fin n) O)
    (hg : Shape α β (g : Matrix (Fin n) (Fin n) O)) :
    ∃! p : Matrix (Fin n) (Fin n) O × (Fin n → Oˣ) × Matrix (Fin n) (Fin n) O,
      UpperUnip α p.1 ∧ LowerUnip β p.2.2 ∧
        (g : Matrix (Fin n) (Fin n) O) = p.1 * Matrix.diagonal (fun i => (p.2.1 i : O)) * p.2.2 := by
  first
  | exact @_root_.GlobalTheory.UnipotentBorder.iwahori_factorisation
  | exact _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation
  | (apply _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnipotentBorder.iwahori_factorisation <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation ..)

theorem existsUnique_factor_opp [IsLocalRing O] {α β : O} (hβ : ¬ IsUnit β) (g : GL (Fin n) O)
    (hg : Shape α β (g : Matrix (Fin n) (Fin n) O)) :
    ∃! p : Matrix (Fin n) (Fin n) O × (Fin n → Oˣ) × Matrix (Fin n) (Fin n) O,
      LowerUnip β p.1 ∧ UpperUnip α p.2.2 ∧
        (g : Matrix (Fin n) (Fin n) O) = p.1 * Matrix.diagonal (fun i => (p.2.1 i : O)) * p.2.2 := by
  obtain ⟨u, d, l, hu, hl, hfac, -⟩ :=
    exists_factor (α := β) (β := α) (by rw [mul_comm]; exact not_isUnit_mul hβ) n _ hg.flip
      (fun i => isUnit_diag hβ (Matrix.isUnits_det_units g) hg i.rev)
  have hfac2 := congrArg flip hfac
  rw [flip_flip, flip_triple] at hfac2
  refine ⟨(flip u, fun i => d i.rev, flip l), ⟨hu.flip, hl.flip, hfac2⟩, ?_⟩
  rintro ⟨l', d', u'⟩ ⟨hl', hu', hfac'⟩
  have hfac3 := congrArg flip hfac'
  rw [flip_triple] at hfac3
  obtain ⟨h1, h2, h3⟩ := factor_unique (d' := fun i => d' i.rev) hu hl'.flip hl hu'.flip
    (hfac.symm.trans hfac3)
  subst h1 h2 h3
  simp [flip_flip]

end General

end GlobalTheory.IwahoriFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisBoundedModuleValuationRingPiStatement
section
open IsDedekindDomain NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_bounded_module_valuationRing_pi : ∀ {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) (d : ℕ) (M : Set (Fin d → F)), (0 : Fin d → F) ∈ M → (∀ x ∈ M, ∀ y ∈ M, x + y ∈ M) → (∀ a : F, p.valuation F a ≤ 1 → ∀ x ∈ M, a • x ∈ M) → (∀ i, Pi.single i 1 ∈ M) → (∃ D : F, D ≠ 0 ∧ ∀ x ∈ M, ∀ i, p.valuation F (D * x i) ≤ 1) → ∃ (m : ℕ) (b : Fin m → Fin d → F), (∀ k, b k ∈ M) ∧ (∀ x ∈ M, ∃ a : Fin m → F, (∀ k, p.valuation F (a k) ≤ 1) ∧ x = ∑ k, a k • b k) ∧ LinearIndependent F b := by
  first | exact @GlobalTheory.locBasis_of_bounded | exact GlobalTheory.locBasis_of_bounded | (intros; apply GlobalTheory.locBasis_of_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCommonDenominatorAevalOfFgStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_aeval_of_fg' : ∀ (O E A : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] (g : A), (∀ x : A, ∃ p : E[X], aeval g p = x) → ∀ S : Submodule O A, S.FG → ∃ c : O, c ≠ 0 ∧ ∀ x ∈ S, ∃ p : O[X], aeval g p = c • x := by
  first | exact @GlobalTheory.exists_common_denominator_aeval_of_fg | exact GlobalTheory.exists_common_denominator_aeval_of_fg | (intros; apply GlobalTheory.exists_common_denominator_aeval_of_fg <;> assumption)
end

