module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CoefLeftAAv
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.VectorComplexifiedDerivativeCommutator
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0003

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.AnaHpartUnique
section
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def inLH {n : ℕ} (H X : Matrix (Fin n) (Fin n) ℂ) : Prop := Xᴴ * H + H * X = 0

section Basic

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}

lemma ana_inv (hH : HInvol H) : H⁻¹ = H := Matrix.inv_eq_left_inv hH.2

lemma ana_isUnit (hH : HInvol H) : IsUnit H := IsUnit.of_mul_eq_one _ hH.2

lemma ana_HH_left (hH : HInvol H) (A : Matrix (Fin n) (Fin n) ℂ) : H * (H * A) = A := by
  rw [← Matrix.mul_assoc, hH.2, Matrix.one_mul]

lemma ana_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) : inUH H (a * b) := by
  unfold inUH at *
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha, hb]

lemma ana_exp (hH : HInvol H) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inLH H Y) :
    inUH H (NormedSpace.exp Y) := by
  have hY' : Yᴴ * H = -(H * Y) := eq_neg_of_add_eq_zero_left hY
  have hYh : Yᴴ = H * (-Y) * H⁻¹ := by
    rw [ana_inv hH, Matrix.mul_neg, ← hY', Matrix.mul_assoc, hH.2, Matrix.mul_one]
  have hexp : (NormedSpace.exp Y)ᴴ = H * NormedSpace.exp (-Y) * H := by
    rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ (ana_isUnit hH), ana_inv hH]
  have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  unfold inUH
  rw [hexp, Matrix.mul_assoc (H * NormedSpace.exp (-Y)) H H, hH.2, Matrix.mul_one, Matrix.mul_assoc, hc,
    Matrix.mul_one]

lemma ana_rsmul {X : Matrix (Fin n) (Fin n) ℂ} (hX : inLH H X) (r : ℝ) : inLH H ((r : ℂ) • X) := by
  unfold inLH at *
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_add, hX, smul_zero]

lemma ana_expt (hH : HInvol H) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inLH H X) (t : ℝ) :
    inUH H (NormedSpace.exp ((t : ℂ) • X)) := ana_exp hH (ana_rsmul hX t)

lemma ana_add {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inLH H A) (hB : inLH H B) : inLH H (A + B) := by
  unfold inLH at *
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
  calc Aᴴ * H + Bᴴ * H + (H * A + H * B) = (Aᴴ * H + H * A) + (Bᴴ * H + H * B) := by abel
    _ = 0 := by rw [hA, hB, add_zero]

lemma ana_neg {A : Matrix (Fin n) (Fin n) ℂ} (hA : inLH H A) : inLH H (-A) := by
  unfold inLH at *
  rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hA, neg_zero]

lemma ana_sub {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inLH H A) (hB : inLH H B) : inLH H (A - B) := by
  rw [sub_eq_add_neg]; exact ana_add hA (ana_neg hB)

lemma ana_bracket {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inLH H X) (hY : inLH H Y) :
    inLH H (X * Y - Y * X) := by
  unfold inLH at *
  have hX' : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
  have hY' : Yᴴ * H = -(H * Y) := eq_neg_of_add_eq_zero_left hY
  have e1 : Yᴴ * Xᴴ * H = H * Y * X := by
    rw [Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, hY', Matrix.neg_mul, neg_neg]
  have e2 : Xᴴ * Yᴴ * H = H * X * Y := by
    rw [Matrix.mul_assoc, hY', Matrix.mul_neg, ← Matrix.mul_assoc, hX', Matrix.neg_mul, neg_neg]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2,
    Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  abel

lemma ana_HXH {X : Matrix (Fin n) (Fin n) ℂ} (hH : HInvol H) (hX : inLH H X) : H * Xᴴ * H = -X := by
  have hX' : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
  rw [Matrix.mul_assoc, hX', Matrix.mul_neg, ana_HH_left hH]

lemma ana_hpart1_eq (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H Z = (1 / 2 : ℂ) • (Z - H * Zᴴ * H) := by
  unfold hpart1; rw [ana_inv hH]

lemma ana_hpart2_eq (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart2 H Z = (1 / (2 * Complex.I) : ℂ) • (Z + H * Zᴴ * H) := by
  unfold hpart2; rw [ana_inv hH]

lemma ana_thetaH (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) : (H * Zᴴ * H)ᴴ * H = H * Z := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hH.1, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, Matrix.mul_assoc, hH.2, Matrix.mul_one]

lemma ana_Htheta (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) : H * (H * Zᴴ * H) = Zᴴ * H := by
  rw [Matrix.mul_assoc, ana_HH_left hH]

lemma ana_hpartMem (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inLH H (hpart1 H Z) ∧ inLH H (hpart2 H Z) ∧ Z = hpart1 H Z + Complex.I • hpart2 H Z ∧
      (inLH H Z → hpart1 H Z = Z ∧ hpart2 H Z = 0) := by
  rw [ana_hpart1_eq hH, ana_hpart2_eq hH]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold inLH
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.sub_mul,
      ana_thetaH hH, Matrix.mul_smul, Matrix.mul_sub, ana_Htheta hH, star_one_half, ← smul_add]
    simp
  · unfold inLH
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.add_mul,
      ana_thetaH hH, Matrix.mul_smul, Matrix.mul_add, ana_Htheta hH, star_one_div_two_I, neg_smul,
      add_comm (H * Z), neg_add_cancel]
  · rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]
    rw [sub_add_add_cancel, ← two_smul ℂ Z, smul_smul]
    norm_num
  · intro hX
    rw [ana_HXH hH hX, sub_neg_eq_add, add_neg_cancel, smul_zero, ← two_smul ℂ Z, smul_smul]
    norm_num

lemma ana_hpart_unique (hH : HInvol H) {P Q : Matrix (Fin n) (Fin n) ℂ} (hP : inLH H P) (hQ : inLH H Q) :
    hpart1 H (P + Complex.I • Q) = P ∧ hpart2 H (P + Complex.I • Q) = Q := by
  have hZ : H * (P + Complex.I • Q)ᴴ * H = -P + Complex.I • Q := by
    rw [conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, ana_HXH hH hP, ana_HXH hH hQ, Complex.star_def, Complex.conj_I]
    module
  rw [ana_hpart1_eq hH, ana_hpart2_eq hH, hZ]
  constructor
  · module
  · have : P + Complex.I • Q + (-P + Complex.I • Q) = (2 * Complex.I) • Q := by module
    rw [this, smul_smul, one_div, inv_mul_cancel₀ (by simp), one_smul]

lemma ana_hpart1_sub (hH : HInvol H) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H (Z - W) = hpart1 H Z - hpart1 H W := by
  rw [ana_hpart1_eq hH, ana_hpart1_eq hH, ana_hpart1_eq hH, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  module

lemma ana_hpart2_sub (hH : HInvol H) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    hpart2 H (Z - W) = hpart2 H Z - hpart2 H W := by
  rw [ana_hpart2_eq hH, ana_hpart2_eq hH, ana_hpart2_eq hH, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  module

lemma ana_hpart1_add (hH : HInvol H) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H (Z + W) = hpart1 H Z + hpart1 H W := by
  rw [ana_hpart1_eq hH, ana_hpart1_eq hH, ana_hpart1_eq hH, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  module

lemma ana_hpart2_add (hH : HInvol H) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    hpart2 H (Z + W) = hpart2 H Z + hpart2 H W := by
  rw [ana_hpart2_eq hH, ana_hpart2_eq hH, ana_hpart2_eq hH, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  module

lemma ana_inv2I : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
  rw [one_div, mul_inv, Complex.inv_I]; ring

lemma ana_hpart1_smul (hH : HInvol H) (x y : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H (((x : ℂ) + (y : ℂ) * Complex.I) • Z) = (x : ℂ) • hpart1 H Z - (y : ℂ) • hpart2 H Z := by
  rw [ana_hpart1_eq hH, ana_hpart1_eq hH, ana_hpart2_eq hH, ana_inv2I, conjTranspose_smul,
    Matrix.mul_smul, Matrix.smul_mul]
  have hs : star ((x : ℂ) + (y : ℂ) * Complex.I) = (x : ℂ) - (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hs]
  match_scalars <;> first | ring1 | linear_combination ((y : ℂ) / 2) * Complex.I_sq | linear_combination (-(y : ℂ) / 2) * Complex.I_sq

lemma ana_hpart2_smul (hH : HInvol H) (x y : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart2 H (((x : ℂ) + (y : ℂ) * Complex.I) • Z) = (x : ℂ) • hpart2 H Z + (y : ℂ) • hpart1 H Z := by
  rw [ana_hpart1_eq hH, ana_hpart2_eq hH, ana_hpart2_eq hH, ana_inv2I, conjTranspose_smul,
    Matrix.mul_smul, Matrix.smul_mul]
  have hs : star ((x : ℂ) + (y : ℂ) * Complex.I) = (x : ℂ) - (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hs]
  match_scalars <;> first | ring1 | linear_combination ((y : ℂ) / 2) * Complex.I_sq | linear_combination (-(y : ℂ) / 2) * Complex.I_sq

end Basic

end AAInvW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CauchyBinet
section
open Matrix Finset

noncomputable section

namespace AAInvW

theorem collapse {A : Type*} [AddCommGroup A] [Module ℂ A] {N r m : ℕ} (hm : m ≤ r)
    (φ : Fin r → Fin N) (hφ : Function.Injective φ) (w : Fin N → Fin N → ℂ)
    (hw : ∀ (a : Fin r) (i : Fin N), (∀ b : Fin r, b.val < a.val → i ≠ φ b) →
      w i (φ a) = if i = φ a then 1 else 0)
    (q : (Fin m → Fin N) → A) (hq : ∀ c : Fin m → Fin N, ¬ Function.Injective c → q c = 0) :
    ∑ c : Fin m → Fin N, (∏ j, w (c j) (φ (Fin.castLE hm j))) • q c =
      q (fun j => φ (Fin.castLE hm j)) := by
  have hone : ∀ j : Fin m, w (φ (Fin.castLE hm j)) (φ (Fin.castLE hm j)) = 1 := by
    intro j
    have h := hw (Fin.castLE hm j) (φ (Fin.castLE hm j)) (fun b hb hb' => by
      have := hφ hb'
      rw [this] at hb
      exact lt_irrefl _ hb)
    rw [h, if_pos rfl]
  rw [Finset.sum_eq_single (fun j => φ (Fin.castLE hm j))]
  · simp only [hone, Finset.prod_const_one, one_smul]
  · intro c _ hc
    by_cases hinj : Function.Injective c
    · have hex : ∃ j, w (c j) (φ (Fin.castLE hm j)) = 0 := by
        by_contra hall
        push_neg at hall
        apply hc
        funext j
        obtain ⟨k, hk⟩ := j
        revert hk
        refine Nat.strong_induction_on k ?_
        intro k ih hk
        by_cases hex : ∃ b : Fin r, b.val < k ∧ c ⟨k, hk⟩ = φ b
        · obtain ⟨b, hbk, hb⟩ := hex
          have hbm : b.val < m := lt_trans hbk hk
          have e1 : c ⟨b.val, hbm⟩ = φ (Fin.castLE hm ⟨b.val, hbm⟩) := ih b.val hbk hbm
          have e2 : Fin.castLE hm ⟨b.val, hbm⟩ = b := Fin.ext rfl
          rw [e2] at e1
          have e3 := hinj (e1.trans hb.symm)
          have e4 : b.val = k := congrArg Fin.val e3
          omega
        · push_neg at hex
          have hw' := hw (Fin.castLE hm ⟨k, hk⟩) (c ⟨k, hk⟩) (fun b hb => hex b hb)
          have hne := hall ⟨k, hk⟩
          rw [hw'] at hne
          by_contra hcon
          exact hne (if_neg hcon)
      obtain ⟨j, hj⟩ := hex
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hj, zero_smul]
    · rw [hq c hinj, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem grouping {A : Type*} [Ring A] [Algebra ℂ A] {t N : ℕ} (κ : Fin N → ℕ) (hκ : Function.Injective κ)
    (F : (Fin t → Fin N) → A)
    (hF : ∀ (d : Fin t → Fin N) (τ : Equiv.Perm (Fin t)),
      F (d ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : A) * F d)
    (hF0 : ∀ d : Fin t → Fin N, ¬ Function.Injective d → F d = 0) (W : (Fin t → Fin N) → ℂ) :
    ∑ d, W d • F d = ∑ C : Fin t → Fin N,
      if StrictMono (fun l => κ (C l)) then
        (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * W (C ∘ σ)) • F C else 0 := by
  classical
  have hR : ∀ C : Fin t → Fin N,
      (if StrictMono (fun l => κ (C l)) then
        (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * W (C ∘ σ)) • F C else 0) =
      ∑ σ : Equiv.Perm (Fin t),
        if StrictMono (fun l => κ (C l)) then W (C ∘ σ) • F (C ∘ σ) else 0 := by
    intro C
    split_ifs with h
    · rw [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [hF C σ, mul_smul]
      first
      | rw [Int.cast_smul_eq_zsmul ℂ, zsmul_eq_mul, mul_smul_comm]
      | simp only [Algebra.smul_def, map_intCast, ← mul_assoc, (Int.cast_commute _ _).eq]
    · simp
  simp only [hR]
  rw [← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => p.1 ∘ p.2) (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · rintro ⟨C, σ⟩ _ h1 ⟨C', σ'⟩ _ h2 heq
    have hC : StrictMono (fun l => κ (C l)) := by
      by_contra hc
      exact h1 (by simp [hc])
    have hC' : StrictMono (fun l => κ (C' l)) := by
      by_contra hc
      exact h2 (by simp [hc])
    have heq' : C ∘ σ = C' ∘ σ' := heq
    have e1 : Set.range (fun l => κ (C l)) = Set.range (fun l => κ (C' l)) := by
      rw [← σ.surjective.range_comp (fun l => κ (C l)), ← σ'.surjective.range_comp (fun l => κ (C' l))]
      congr 1
      funext x
      exact congrArg κ (congrFun heq' x)
    have e2 : (fun l => κ (C l)) = (fun l => κ (C' l)) := by
      first
      | exact (StrictMono.range_inj hC hC').1 e1
      | exact (WellFounded.eq_strictMono_iff_eq_range wellFounded_lt hC hC').1 e1
    have e3 : C = C' := funext fun l => hκ (congrFun e2 l)
    subst e3
    have e4 : σ = σ' := Equiv.ext fun x => hC.injective (congrArg κ (congrFun heq' x))
    rw [e4]
  · intro d _ hd
    have hinj : Function.Injective d := by
      by_contra hni
      apply hd
      simp [hF0 d hni]
    have hmono : Monotone ((fun l => κ (d l)) ∘ Tuple.sort (fun l => κ (d l))) :=
      Tuple.monotone_sort _
    have hsm : StrictMono (fun l => κ ((d ∘ Tuple.sort (fun l => κ (d l))) l)) :=
      hmono.strictMono_of_injective ((hκ.comp hinj).comp (Tuple.sort (fun l => κ (d l))).injective)
    have hcomp : (d ∘ Tuple.sort (fun l => κ (d l))) ∘ (Tuple.sort (fun l => κ (d l))).symm = d := by
      funext x
      simp
    refine ⟨(d ∘ Tuple.sort (fun l => κ (d l)), (Tuple.sort (fun l => κ (d l))).symm),
      Finset.mem_univ _, ?_, ?_⟩
    · dsimp only
      rw [if_pos hsm, hcomp]
      exact hd
    · exact hcomp
  · rintro ⟨C, σ⟩ _ h1
    have hC : StrictMono (fun l => κ (C l)) := by
      by_contra hc
      exact h1 (by simp [hc])
    dsimp only
    rw [if_pos hC]

theorem det_mul_expand {m N : ℕ} (X : Matrix (Fin m) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin m) ℂ) :
    (X * Y).det = ∑ d : Fin m → Fin N, (∏ l, Y (d l) l) • (Matrix.of fun a l => X a (d l)).det := by
  rw [← Matrix.det_transpose]
  have hT : (X * Y)ᵀ = fun l => ∑ k, Y k l • (fun a => X a k) := by
    ext l a
    simp [Matrix.transpose_apply, Matrix.mul_apply, Finset.sum_apply, mul_comm]
  rw [hT]
  refine ((Matrix.detRowAlternating (R := ℂ) (n := Fin m)).toMultilinearMap.map_sum
    (fun l k => Y k l • (fun a => X a k))).trans ?_
  refine Finset.sum_congr rfl (fun d _ => ?_)
  refine ((Matrix.detRowAlternating (R := ℂ) (n := Fin m)).toMultilinearMap.map_smul_univ
    (fun l => Y (d l) l) (fun l a => X a (d l))).trans ?_
  congr 1
  rw [← Matrix.det_transpose]
  rfl

theorem cauchyBinet {m N : ℕ} (κ : Fin N → ℕ) (hκ : Function.Injective κ)
    (X : Matrix (Fin m) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin m) ℂ) :
    (X * Y).det = ∑ C : Fin m → Fin N,
      if StrictMono (fun l => κ (C l)) then
        (Matrix.of fun a l => X a (C l)).det * (Matrix.of fun i l => Y (C i) l).det else 0 := by
  have hF : ∀ (d : Fin m → Fin N) (τ : Equiv.Perm (Fin m)),
      (Matrix.of fun a l => X a ((d ∘ τ) l)).det =
        ((Equiv.Perm.sign τ : ℤ) : ℂ) * (Matrix.of fun a l => X a (d l)).det := by
    intro d τ
    exact Matrix.det_permute' τ (Matrix.of fun a l => X a (d l))
  have hF0 : ∀ d : Fin m → Fin N, ¬ Function.Injective d → (Matrix.of fun a l => X a (d l)).det = 0 := by
    intro d hd
    simp only [Function.Injective, not_forall] at hd
    obtain ⟨p, q, hpq, hne⟩ := hd
    exact Matrix.det_zero_of_column_eq hne (fun a => by simp [hpq])
  rw [det_mul_expand X Y]
  rw [grouping κ hκ (fun d => (Matrix.of fun a l => X a (d l)).det) hF hF0 (fun d => ∏ l, Y (d l) l)]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  split_ifs with h
  · rw [smul_eq_mul, mul_comm]
    congr 1
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp [Units.smul_def, zsmul_eq_mul]
  · rfl

end AAInvW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.HkConjTranspose
section
open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

def hkSig (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by split_ifs <;> omega⟩

def hkEps (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hk_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = hkSig k r i then hkEps k r i else 0 := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only [Hpk, hkSig, hkEps, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hk_sig_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : hkSig k r (hkSig k r i) = i := by
  apply Fin.ext
  simp only [hkSig]
  split_ifs <;> omega

theorem hk_eps_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : hkEps k r (hkSig k r i) = hkEps k r i := by
  simp only [hkEps, hkSig]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hk_eps_mul_self (k r : ℕ) (i : Fin (2 * r + k + 1)) : hkEps k r i * hkEps k r i = 1 := by
  unfold hkEps
  split_ifs <;> norm_num

theorem hk_star_eps (k r : ℕ) (i : Fin (2 * r + k + 1)) : star (hkEps k r i) = hkEps k r i := by
  unfold hkEps
  split_ifs <;> simp

theorem hk_mul_self (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp_rw [hk_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    hk_sig_sig, hk_eps_sig]
  by_cases h : j = i
  · subst h; simp [hk_eps_mul_self]
  · simp [h, one_apply_ne' h]

theorem hk_conjTranspose (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, hk_apply, hk_apply]
  by_cases h : j = hkSig k r i
  · subst h
    simp [hk_sig_sig, hk_eps_sig, hk_star_eps]
  · have h' : i ≠ hkSig k r j := fun e => h (by rw [e, hk_sig_sig])
    simp [h, h']

theorem hpk_involution : HpkInvol := fun k r => ⟨hk_conjTranspose k r, hk_mul_self k r⟩

end AAInvW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.OpModel
section
open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

def OpModel : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), HInvol H →
    ∃ (M : Submodule ℂ ({x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E))
      (cls : (Matrix (Fin n) (Fin n) ℂ → E) → M) (Eh : Fin n → Fin n → Module.End ℂ M),
      GlRel Eh ∧
      (∀ (t : ℕ) (a b : Fin t → Fin n) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
          (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUH H g),
        SmoothOnH H f → qminorOp (EabH H) a b u f g = ((qminor Eh a b u (cls f) : M) : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) ⟨g, hg⟩) ∧
      ∀ s : Matrix (Fin n) (Fin n) ℂ, inUH H s → ∃ ρ : Module.End ℂ M,
        (∀ f : Matrix (Fin n) (Fin n) ℂ → E, SmoothOnH H f → cls (fun x => f (x * s)) = ρ (cls f)) ∧
        (∀ (ψ : M) (y : Matrix (Fin n) (Fin n) ℂ) (hy : inUH H y) (y' : Matrix (Fin n) (Fin n) ℂ)
            (hy' : inUH H y'), y' = y * s → ((ρ ψ : M) : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) ⟨y, hy⟩ = (ψ : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) ⟨y', hy'⟩) ∧
        ∀ a b : Fin n, Eh a b * ρ = ρ * ∑ c, ∑ d, (s⁻¹ c a * s b d) • Eh c d

end AAInvW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.OperatorsCommuteTranslationsOfLeftRight
section
open Matrix

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem inUH_mul {n : ℕ} {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) :
    inUH H (a * b) := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

theorem operators_commute_translations_of_left_right (hL : LeftAA) (hR : RightAA) (hS : SsetUH) : OperatorsCommuteTranslations := by
  unfold OperatorsCommuteTranslations
  intro E _ _ k r z z' m hm u ell f _ _ hf s hs s' hs' g hg
  have hsg : inUH (Hpk k r) (s * g) := inUH_mul (hS k r z s hs) hg
  obtain ⟨hL1, hL2⟩ := hL E k r z m hm u ell (fun x => f (x * s')) s g hs hg
  obtain ⟨hR1, hR2⟩ := hR E k r z' m hm u ell f s' (s * g) hf hs' hsg
  exact ⟨hL1.trans hR1, hL2.trans hR2⟩

end AAInvW
end
end

