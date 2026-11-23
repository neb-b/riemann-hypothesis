module

public import Formalism.HermitianCurvature.StatementG
public import Formalism.HermitianCurvature.Bundle0001

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RemainderNormLeStrictUpper
section
open Matrix

namespace Formalism.FourierDecayAlt.P.G6

open Formalism.FourierDecayAlt.G

theorem blk_cc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk A b a e i.castSucc j.castSucc = A i j := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  simp [blk, h]

theorem blk_cl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  have h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
  simp [blk, h, h2]

theorem xOf_castSucc {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ)
    (k : Fin m) : xOf X B k.castSucc = X k.castSucc k.succ := by
  rw [xOf, Fin.succ_castSucc, blk_cc]

theorem xOf_last {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ) :
    xOf X B (Fin.last m) = B (Fin.last m) := by
  rw [xOf, Fin.succ_last, blk_cl]

theorem isStrictUpper_strictUpper {d : ℕ} (v : UT d → ℂ) : IsStrictUpper (strictUpper v) := by
  intro i j h
  simp [strictUpper, not_lt.mpr h]

theorem isStrictUpper_neg {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsStrictUpper X) :
    IsStrictUpper (-X) := by
  intro i j h
  simp [hX i j h]

theorem pow_apply_eq_zero {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsStrictUpper X) (k : ℕ) :
    ∀ i j : Fin d, (j : ℕ) < i + k → (X ^ k) i j = 0 := by
  induction k with
  | zero =>
    intro i j h
    rw [pow_zero]
    refine Matrix.one_apply_ne ?_
    intro e
    subst e
    simp at h
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : (l : ℕ) < i + k
    · rw [ih i l hl, zero_mul]
    · rw [hX l j (by rw [Fin.le_def]; omega), mul_zero]

theorem pow_apply_zero {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hX : IsStrictUpper X) :
    ∀ (j : ℕ) (hj : j < m + 1), (X ^ j) 0 ⟨j, hj⟩ =
      ∏ k : Fin j, X ⟨k, by omega⟩ ⟨k + 1, by omega⟩ := by
  intro j
  induction j with
  | zero => intro hj; simp
  | succ j ih =>
    intro hj
    rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single (⟨j, by omega⟩ : Fin (m + 1)),
      ih (by omega), Fin.prod_univ_castSucc]
    · rfl
    · intro l _ hl
      by_cases h : (l : ℕ) < j
      · rw [pow_apply_eq_zero hX j 0 l (by simpa using h), zero_mul]
      · have h2 : (l : ℕ) ≠ j := fun e => hl (Fin.ext e)
        rw [hX l ⟨j + 1, hj⟩ (by rw [Fin.le_def]; simp only; omega), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem pow_mulVec_zero {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hX : IsStrictUpper X)
    (B : Fin (m + 1) → ℂ) : (X ^ m *ᵥ B) 0 = ∏ k, xOf X B k := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (Fin.last m), Fin.prod_univ_castSucc, xOf_last]
  · congr 1
    have := pow_apply_zero hX m (Nat.lt_succ_self m)
    rw [show (Fin.last m) = ⟨m, Nat.lt_succ_self m⟩ from rfl, this]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [xOf_castSucc]
    rfl
  · intro l _ hl
    have h2 : (l : ℕ) ≠ m := fun e => hl (Fin.ext e)
    have h3 := l.2
    rw [pow_apply_eq_zero hX m 0 l (by simp only [Fin.val_zero]; omega), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem pow_mulVec_succ {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hX : IsStrictUpper X)
    (B : Fin (m + 1) → ℂ) (k : Fin m) : (X ^ m *ᵥ B) k.succ = 0 := by
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [pow_apply_eq_zero hX m k.succ l (by have := l.2; simp only [Fin.val_succ]; omega), zero_mul]

theorem sum_mul_zero_pow (m : ℕ) (f : ℕ → ℂ) :
    ∑ j ∈ Finset.range (m + 1), f j * (0 : ℂ) ^ (m - j) = f m := by
  rw [Finset.sum_range_succ, Finset.sum_eq_zero, Nat.sub_self, pow_zero, mul_one, zero_add]
  intro j hj
  have := Finset.mem_range.mp hj
  rw [zero_pow (by omega), mul_zero]

theorem norm_pow_mulVec_le {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} {B : Fin (m + 1) → ℂ}
    {L : ℝ} (hL : 0 ≤ L) (hX : ∀ i j, ‖X i j‖ ≤ L) (hB : ∀ i, ‖B i‖ ≤ L) (j : ℕ) :
    ∀ i, ‖((-X) ^ j *ᵥ B) i‖ ≤ ((m : ℝ) + 1) ^ j * L ^ (j + 1) := by
  induction j with
  | zero => intro i; simpa using hB i
  | succ j ih =>
    intro i
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct]
    calc ‖∑ l, (-X) i l * ((-X) ^ j *ᵥ B) l‖ ≤ ∑ l, ‖(-X) i l * ((-X) ^ j *ᵥ B) l‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _l : Fin (m + 1), L * (((m : ℝ) + 1) ^ j * L ^ (j + 1)) := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [norm_mul]
          refine mul_le_mul ?_ (ih l) (norm_nonneg _) hL
          simpa using hX i l
      _ = ((m : ℝ) + 1) ^ (j + 1) * L ^ (j + 1 + 1) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring

theorem remainder_norm_le_strict_upper {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} {B : Fin (m + 1) → ℂ}
    {ρ' : Fin m → ℂ} {t : ℂ} {L : ℝ} (hL : 1 ≤ L) (ht : ‖t‖ ≤ 1) (hS : IsStrictUpper X)
    (hX : ∀ i j, ‖X i j‖ ≤ L) (hB : ∀ i, ‖B i‖ ≤ L) (hρ : ∀ k, ‖ρ' k‖ ≤ L) :
    ‖R0 X B ρ' t‖ ≤ (((m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1) ^ m)) * (L ^ (m + 2) * ‖t‖) := by
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have term : ∀ j ∈ Finset.range (m + 1),
      ‖(∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ) * t ^ (m - j)‖ ≤
        ((m : ℝ) * ((m : ℝ) + 1) ^ m) * (L ^ (m + 2) * ‖t‖) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    by_cases hjm : j = m
    · subst hjm
      rw [Finset.sum_eq_zero, zero_mul, norm_zero]
      · positivity
      · intro k _
        rw [pow_mulVec_succ (isStrictUpper_neg hS), mul_zero]
    · have hlt : j < m := by omega
      rw [norm_mul, norm_pow]
      have h1 : ‖∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ‖ ≤
          (m : ℝ) * ((m : ℝ) + 1) ^ m * L ^ (m + 2) := by
        calc ‖∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ‖
            ≤ ∑ k : Fin m, ‖ρ' k * ((-X) ^ j *ᵥ B) k.succ‖ := norm_sum_le _ _
          _ ≤ ∑ _k : Fin m, L * (((m : ℝ) + 1) ^ j * L ^ (j + 1)) := by
              refine Finset.sum_le_sum fun k _ => ?_
              rw [norm_mul]
              exact mul_le_mul (hρ k) (norm_pow_mulVec_le hL0 hX hB j k.succ) (norm_nonneg _) hL0
          _ = (m : ℝ) * (((m : ℝ) + 1) ^ j * L ^ (j + 2)) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              ring
          _ ≤ (m : ℝ) * (((m : ℝ) + 1) ^ m * L ^ (m + 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg m)
              refine mul_le_mul (pow_le_pow_right₀ hm1 hlt.le) (pow_le_pow_right₀ hL (by omega))
                (by positivity) (by positivity)
          _ = (m : ℝ) * ((m : ℝ) + 1) ^ m * L ^ (m + 2) := by ring
      have h2 : ‖t‖ ^ (m - j) ≤ ‖t‖ := pow_le_of_le_one (norm_nonneg _) ht (by omega)
      calc ‖∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ‖ * ‖t‖ ^ (m - j)
          ≤ ((m : ℝ) * ((m : ℝ) + 1) ^ m * L ^ (m + 2)) * ‖t‖ :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = _ := by ring
  calc ‖R0 X B ρ' t‖ ≤ ∑ j ∈ Finset.range (m + 1),
        ‖(∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ) * t ^ (m - j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (m + 1), ((m : ℝ) * ((m : ℝ) + 1) ^ m) * (L ^ (m + 2) * ‖t‖) :=
        Finset.sum_le_sum term
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

theorem rpow_bound (m : ℕ) {T ε : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hε : ε ≤ 1 / (2 * ((m : ℝ) + 2))) : (T ^ (-ε)) ^ (m + 2) * T ≤ Real.sqrt T := by
  have hm : (0 : ℝ) < 2 * ((m : ℝ) + 2) := by positivity
  have h1 : ε * (2 * ((m : ℝ) + 2)) ≤ 1 := (le_div_iff₀ hm).mp hε
  have e : (T ^ (-ε)) ^ (m + 2) * T = T ^ (-ε * ((m : ℝ) + 2) + 1) := by
    rw [Real.rpow_add hT, Real.rpow_one, Real.rpow_mul hT.le, ← Real.rpow_natCast]
    push_cast
    rfl
  rw [e, Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_ge hT hT1 (by nlinarith)

end Formalism.FourierDecayAlt.P.G6

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G6

theorem leading_cofactor : Formalism.FourierDecayAlt.G.CofLead := by
  intro m X B ρ' hX
  constructor
  · rw [Cof, sum_mul_zero_pow m (fun j => ((-X) ^ j *ᵥ B) 0)]
    have e : (-X) ^ m = ((-1 : ℂ) ^ m) • X ^ m := by
      rw [← smul_pow, neg_one_smul]
    rw [e, Matrix.smul_mulVec, Pi.smul_apply, pow_mulVec_zero hX, smul_eq_mul]
  · rw [R0, sum_mul_zero_pow m (fun j => ∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [pow_mulVec_succ (isStrictUpper_neg hX), mul_zero]

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleInv
section
namespace Formalism.FourierDecayAlt.R.PInv

open Matrix LevelData

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem comm_mat_prod (x : A) :
    ∀ l : List (Matrix (Fin 2) (Fin 2) A), (∀ M ∈ l, ∀ i j, Commute x (M i j)) →
      ∀ i j, Commute x (l.prod i j)
  | [], _ => by
      intro i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | M :: l, h => by
      intro i j
      rw [List.prod_cons, Matrix.mul_apply]
      exact Commute.sum_right _ _ _ fun k _ =>
        (h M (by simp) i k).mul_right (comm_mat_prod x l (fun N hN => h N (by simp [hN])) k j)

theorem prod_mul_prod_eq_one : ∀ (n : ℕ) (f g : Fin n → A), (∀ i, f i * g i = 1) →
    (∀ i j, Commute (f i) (g j)) → (List.ofFn f).prod * (List.ofFn g).prod = 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro f g h1 hc
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
      have hP : Commute (List.ofFn fun i => f i.succ).prod (g 0) :=
        Commute.list_prod_left _ _ (by
          intro a ha
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
          exact hc _ _)
      have hTail := ih (fun i => f i.succ) (fun i => g i.succ)
        (fun i => h1 _) (fun i j => hc _ _)
      calc
        _ = f 0 * g 0 * ((List.ofFn fun i => f i.succ).prod * (List.ofFn fun i => g i.succ).prod) :=
          hP.mul_mul_mul_comm _ _
        _ = 1 := by rw [h1 0, hTail, mul_one]

variable {r : ℕ} (L : LevelData A r)

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_fcomm {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) : Commute x y :=
  L.fns_comm x hx y hy

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_cb (l) : L.cb l ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_cbi (l) : L.cbi l ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_c (l) : L.c l ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_ci (l) : L.ci l ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_ζ : L.ζ ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_ζi : L.ζi ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_ζb : L.ζb ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_ζbi : L.ζbi ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_GG : L.GG ∈ L.fns := by simp [LevelData.fns]
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_mem_GGi : L.GGi ∈ L.fns := by simp [LevelData.fns]

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_comm_ofFn {x : A} {f : Fin r → A} (h : ∀ i, Commute x (f i)) :
    Commute x (List.ofFn f).prod :=
  Commute.list_prod_right _ _ (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact h i)

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_comm_Tprod {x : A} (hp : ∀ l, Commute x (L.p l)) (hc : ∀ l, Commute x (L.c l))
    (hci : ∀ l, Commute x (L.ci l)) (Y : ℂ) (i j) : Commute x (L.Tprod Y i j) := by
  apply comm_mat_prod
  intro M hM
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hM)
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [LevelData.Tl, (hp l).add_left, Algebra.commutes, hc l, hci l, Commute.neg_right,
      Commute.add_right, Commute.zero_right]
  exact Commute.add_right (Algebra.commute_algebraMap_right Y x) (hp l)

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_comm_Tvprod {x : A} (hp : ∀ l, Commute x (L.pb l)) (hc : ∀ l, Commute x (L.cb l))
    (hci : ∀ l, Commute x (L.cbi l)) (Y : ℂ) (i j) : Commute x (L.Tvprod Y i j) := by
  apply comm_mat_prod
  intro M hM
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hM)
  intro i j
  fin_cases i <;> fin_cases j <;> simp [LevelData.Tvl, hc l, hci l]
  exact Commute.sub_right (Algebra.commute_algebraMap_right Y x) (hp l)

theorem comm_alg (x : A) (y : ℂ) : Commute x (algebraMap ℂ A y) := Algebra.commute_algebraMap_right y x

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_S_mem {x : A} (hx : x ∈ L.fns) : x ∈ Algebra.adjoin ℂ L.fns := Algebra.subset_adjoin hx

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_S_prod {f : Fin r → A} (hf : ∀ i, f i ∈ L.fns) :
    (List.ofFn f).prod ∈ Algebra.adjoin ℂ L.fns :=
  Subalgebra.list_prod_mem _ (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact L.inv_S_mem (hf i))

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_Drb_Drbi : L.Drb * L.Drbi = 1 :=
  prod_mul_prod_eq_one r L.cb L.cbi L.cb_cbi (fun i j => L.inv_fcomm (L.inv_mem_cb i) (L.inv_mem_cbi j))
theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_Dr_Dri : L.Dr * L.Dri = 1 :=
  prod_mul_prod_eq_one r L.c L.ci L.c_ci (fun i j => L.inv_fcomm (L.inv_mem_c i) (L.inv_mem_ci j))

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_hR_bar (Y : ℂ) :
    L.G * L.Dbi * L.Dbi * L.Ahatv Y = L.Dr * L.GG * (L.ζbi * L.ζbi * L.Avr Y) := by
  open scoped IsMulCommutative in
  letI : IsMulCommutative (Algebra.adjoin ℂ L.fns) := Algebra.isMulCommutative_adjoin ℂ (by
    intro x hx y hy _
    exact L.fns_comm x hx y hy)
  let Dr' : Algebra.adjoin ℂ L.fns := ⟨L.Dr, L.inv_S_prod L.inv_mem_c⟩
  let Drb' : Algebra.adjoin ℂ L.fns := ⟨L.Drb, L.inv_S_prod L.inv_mem_cb⟩
  let Drbi' : Algebra.adjoin ℂ L.fns := ⟨L.Drbi, L.inv_S_prod L.inv_mem_cbi⟩
  let GG' : Algebra.adjoin ℂ L.fns := ⟨L.GG, L.inv_S_mem L.inv_mem_GG⟩
  let z' : Algebra.adjoin ℂ L.fns := ⟨L.ζbi, L.inv_S_mem L.inv_mem_ζbi⟩
  have h1 : Drb' * Drbi' = 1 := Subtype.ext L.inv_Drb_Drbi
  have hS : Dr' * Drb' * GG' * (z' * Drbi') * (z' * Drbi') * Drb' = Dr' * GG' * (z' * z') := by
    calc
      _ = Dr' * GG' * (z' * z') * ((Drb' * Drbi') * (Drb' * Drbi')) := by ring
      _ = _ := by rw [h1]; simp
  have hA := congrArg Subtype.val hS
  simp only [LevelData.G, LevelData.Dbi, LevelData.Ahatv]
  calc L.Dr * L.Drb * L.GG * (L.ζbi * L.Drbi) * (L.ζbi * L.Drbi) * (L.Drb * L.Avr Y)
      = (L.Dr * L.Drb * L.GG * (L.ζbi * L.Drbi) * (L.ζbi * L.Drbi) * L.Drb) * L.Avr Y := by
        noncomm_ring
    _ = (L.Dr * L.GG * (L.ζbi * L.ζbi)) * L.Avr Y := by rw [show L.Dr * L.Drb * L.GG * (L.ζbi * L.Drbi) * (L.ζbi * L.Drbi) * L.Drb = L.Dr * L.GG * (L.ζbi * L.ζbi) from hA]
    _ = L.Dr * L.GG * (L.ζbi * L.ζbi * L.Avr Y) := by noncomm_ring

theorem _root_.Formalism.FourierDecayAlt.R.LevelData.inv_hR_hol (Y : ℂ) :
    L.G * L.Di * L.Di * L.Ahat Y = L.Drb * L.GG * (L.ζi * L.ζi * L.Ar Y) := by
  open scoped IsMulCommutative in
  letI : IsMulCommutative (Algebra.adjoin ℂ L.fns) := Algebra.isMulCommutative_adjoin ℂ (by
    intro x hx y hy _
    exact L.fns_comm x hx y hy)
  let Dr' : Algebra.adjoin ℂ L.fns := ⟨L.Dr, L.inv_S_prod L.inv_mem_c⟩
  let Drb' : Algebra.adjoin ℂ L.fns := ⟨L.Drb, L.inv_S_prod L.inv_mem_cb⟩
  let Dri' : Algebra.adjoin ℂ L.fns := ⟨L.Dri, L.inv_S_prod L.inv_mem_ci⟩
  let GG' : Algebra.adjoin ℂ L.fns := ⟨L.GG, L.inv_S_mem L.inv_mem_GG⟩
  let z' : Algebra.adjoin ℂ L.fns := ⟨L.ζi, L.inv_S_mem L.inv_mem_ζi⟩
  have h1 : Dr' * Dri' = 1 := Subtype.ext L.inv_Dr_Dri
  have hS : Dr' * Drb' * GG' * (z' * Dri') * (z' * Dri') * Dr' = Drb' * GG' * (z' * z') := by
    calc
      _ = Drb' * GG' * (z' * z') * ((Dr' * Dri') * (Dr' * Dri')) := by ring
      _ = _ := by rw [h1]; simp
  have hA := congrArg Subtype.val hS
  simp only [LevelData.G, LevelData.Di, LevelData.Ahat]
  calc L.Dr * L.Drb * L.GG * (L.ζi * L.Dri) * (L.ζi * L.Dri) * (L.Dr * L.Ar Y)
      = (L.Dr * L.Drb * L.GG * (L.ζi * L.Dri) * (L.ζi * L.Dri) * L.Dr) * L.Ar Y := by
        noncomm_ring
    _ = (L.Drb * L.GG * (L.ζi * L.ζi)) * L.Ar Y := by rw [show L.Dr * L.Drb * L.GG * (L.ζi * L.Dri) * (L.ζi * L.Dri) * L.Dr = L.Drb * L.GG * (L.ζi * L.ζi) from hA]
    _ = L.Drb * L.GG * (L.ζi * L.ζi * L.Ar Y) := by noncomm_ring

theorem ruleInv : RuleInv := by
  intro A _ _ r L Y

  have zb_p : ∀ l, Commute L.ζbi (L.p l) := fun l => (L.p_ζbi l).symm
  have zb_pb : ∀ l, Commute L.ζbi (L.pb l) := fun l => (L.pb_ζbi l).symm
  have z_p : ∀ l, Commute L.ζi (L.p l) := fun l => (L.p_ζi l).symm
  have z_pb : ∀ l, Commute L.ζi (L.pb l) := fun l => (L.pb_ζi l).symm
  have fc := fun {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) => L.inv_fcomm hx hy
  have zbAr : ∀ i j, Commute L.ζbi (L.Tprod Y i j) :=
    L.inv_comm_Tprod zb_p (fun l => fc L.inv_mem_ζbi (L.inv_mem_c l)) (fun l => fc L.inv_mem_ζbi (L.inv_mem_ci l)) Y
  have zbAv : ∀ i j, Commute L.ζbi (L.Tvprod Y i j) :=
    L.inv_comm_Tvprod zb_pb (fun l => fc L.inv_mem_ζbi (L.inv_mem_cb l)) (fun l => fc L.inv_mem_ζbi (L.inv_mem_cbi l)) Y
  have zAr : ∀ i j, Commute L.ζi (L.Tprod Y i j) :=
    L.inv_comm_Tprod z_p (fun l => fc L.inv_mem_ζi (L.inv_mem_c l)) (fun l => fc L.inv_mem_ζi (L.inv_mem_ci l)) Y
  have zAv : ∀ i j, Commute L.ζi (L.Tvprod Y i j) :=
    L.inv_comm_Tvprod z_pb (fun l => fc L.inv_mem_ζi (L.inv_mem_cb l)) (fun l => fc L.inv_mem_ζi (L.inv_mem_cbi l)) Y
  have zbDr : Commute L.ζbi L.Dr := LevelData.inv_comm_ofFn fun l => fc L.inv_mem_ζbi (L.inv_mem_c l)
  have zbDrb : Commute L.ζbi L.Drb := LevelData.inv_comm_ofFn fun l => fc L.inv_mem_ζbi (L.inv_mem_cb l)
  have zDr : Commute L.ζi L.Dr := LevelData.inv_comm_ofFn fun l => fc L.inv_mem_ζi (L.inv_mem_c l)
  have zDrb : Commute L.ζi L.Drb := LevelData.inv_comm_ofFn fun l => fc L.inv_mem_ζi (L.inv_mem_cb l)
  have zbGG : Commute L.ζbi L.GG := fc L.inv_mem_ζbi L.inv_mem_GG
  have zGG : Commute L.ζi L.GG := fc L.inv_mem_ζi L.inv_mem_GG
  have zb_l0 : Commute L.ζbi (L.l0 Y) := by
    simp only [LevelData.l0]
    exact ((show Commute L.ζbi L.nab from L.nab_ζbi.symm).neg_right).sub_right ((comm_alg _ _).mul_right
      ((fc L.inv_mem_ζbi L.inv_mem_ζb).mul_right (fc L.inv_mem_ζbi L.inv_mem_GGi)))
  have z_m0 : Commute L.ζi (L.m0 Y) := by
    simp only [LevelData.m0]
    exact ((show Commute L.ζi L.nabs from L.nabs_ζi.symm).neg_right).sub_right ((comm_alg _ _).mul_right
      ((fc L.inv_mem_ζi L.inv_mem_ζ).mul_right (fc L.inv_mem_ζi L.inv_mem_GGi)))
  have hm : L.m0 Y * L.ζbi = L.ζbi * L.m0 Y - L.ζbi * L.ζbi := by
    have hX : Commute L.ζbi (algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi)) :=
      (comm_alg _ _).mul_right ((fc L.inv_mem_ζbi L.inv_mem_ζ).mul_right (fc L.inv_mem_ζbi L.inv_mem_GGi))
    simp only [LevelData.m0]
    calc (-L.nabs - algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi)) * L.ζbi
        = -(L.nabs * L.ζbi) - algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi) * L.ζbi := by noncomm_ring
      _ = -(L.ζbi * L.nabs + L.ζbi * L.ζbi) - L.ζbi * (algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi)) := by
          rw [L.nabs_ζbi, hX.eq]
      _ = _ := by noncomm_ring
  have hl : L.l0 Y * L.ζi = L.ζi * L.l0 Y + L.ζi * L.ζi := by
    have hX : Commute L.ζi (algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi)) :=
      (comm_alg _ _).mul_right ((fc L.inv_mem_ζi L.inv_mem_ζb).mul_right (fc L.inv_mem_ζi L.inv_mem_GGi))
    simp only [LevelData.l0]
    calc (-L.nab - algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi)) * L.ζi
        = -(L.nab * L.ζi) - algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi) * L.ζi := by noncomm_ring
      _ = -(L.ζi * L.nab - L.ζi * L.ζi) - L.ζi * (algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi)) := by
          rw [L.nab_ζi, hX.eq]
      _ = _ := by noncomm_ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (zbDr.mul_right (zbAr 0 0)).eq
  · exact ((zbDrb.mul_right zbGG).mul_right ((zb_l0.mul_right (zbAr 0 0)).add_right (zbAr 1 0))).eq
  · exact (zbDrb.mul_right (zbAv 0 0)).eq
  · rw [inv_hR_bar]
    have e1 : (L.m0 Y * L.Avr Y + L.Bvr Y) * L.ζbi
        = (L.ζbi * L.m0 Y - L.ζbi * L.ζbi) * L.Avr Y + L.ζbi * L.Bvr Y := by
      have hA1 : Commute L.ζbi (L.Avr Y) := zbAv 0 0
      have hB1 : Commute L.ζbi (L.Bvr Y) := zbAv 1 0
      rw [add_mul, mul_assoc, ← hA1.eq, ← mul_assoc, hm, ← hB1.eq]
    have hDG : Commute L.ζbi (L.Dr * L.GG) := zbDr.mul_right zbGG
    simp only [LevelData.R0v]
    calc L.Dr * L.GG * (L.m0 Y * L.Avr Y + L.Bvr Y) * L.ζbi - L.ζbi * (L.Dr * L.GG * (L.m0 Y * L.Avr Y + L.Bvr Y))
        = L.Dr * L.GG * ((L.m0 Y * L.Avr Y + L.Bvr Y) * L.ζbi) - (L.ζbi * (L.Dr * L.GG)) * (L.m0 Y * L.Avr Y + L.Bvr Y) := by
          noncomm_ring
      _ = L.Dr * L.GG * ((L.ζbi * L.m0 Y - L.ζbi * L.ζbi) * L.Avr Y + L.ζbi * L.Bvr Y) - (L.Dr * L.GG * L.ζbi) * (L.m0 Y * L.Avr Y + L.Bvr Y) := by
          rw [e1, hDG.eq]
      _ = _ := by noncomm_ring
  · exact (zDr.mul_right (zAr 0 0)).eq
  · exact (zDrb.mul_right (zAv 0 0)).eq
  · exact ((zDr.mul_right zGG).mul_right ((z_m0.mul_right (zAv 0 0)).add_right (zAv 1 0))).eq
  · rw [inv_hR_hol]
    have e1 : (L.l0 Y * L.Ar Y + L.Br Y) * L.ζi
        = (L.ζi * L.l0 Y + L.ζi * L.ζi) * L.Ar Y + L.ζi * L.Br Y := by
      have hA1 : Commute L.ζi (L.Ar Y) := zAr 0 0
      have hB1 : Commute L.ζi (L.Br Y) := zAr 1 0
      rw [add_mul, mul_assoc, ← hA1.eq, ← mul_assoc, hl, ← hB1.eq]
    have hDG : Commute L.ζi (L.Drb * L.GG) := zDrb.mul_right zGG
    simp only [LevelData.R0]
    calc L.Drb * L.GG * (L.l0 Y * L.Ar Y + L.Br Y) * L.ζi - L.ζi * (L.Drb * L.GG * (L.l0 Y * L.Ar Y + L.Br Y))
        = L.Drb * L.GG * ((L.l0 Y * L.Ar Y + L.Br Y) * L.ζi) - (L.ζi * (L.Drb * L.GG)) * (L.l0 Y * L.Ar Y + L.Br Y) := by
          noncomm_ring
      _ = L.Drb * L.GG * ((L.ζi * L.l0 Y + L.ζi * L.ζi) * L.Ar Y + L.ζi * L.Br Y) - (L.Drb * L.GG * L.ζi) * (L.l0 Y * L.Ar Y + L.Br Y) := by
          rw [e1, hDG.eq]
      _ = _ := by noncomm_ring

end Formalism.FourierDecayAlt.R.PInv

theorem Formalism.FourierDecayAlt.P.inverseCommutators : Formalism.FourierDecayAlt.R.RuleInv := Formalism.FourierDecayAlt.R.PInv.ruleInv
end

