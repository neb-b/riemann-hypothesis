module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0038

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariants
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.NormalFormL

variable {k : Type} [Field k] {r : ℕ}

def ev (r : ℕ) (k : Type) [Field k] (i : ℕ) : Fin r → k := fun j => if (j : ℕ) = i then 1 else 0

theorem ev_eq_single (i : ℕ) (hi : i < r) : ev r k i = Pi.single (⟨i, hi⟩ : Fin r) 1 := by
  funext j
  simp only [ev, Pi.single_apply, Fin.ext_iff]

theorem sum_mulVec' {ι : Type} (s : Finset ι) (M : ι → Matrix (Fin r) (Fin r) k) (v : Fin r → k) :
    (∑ i ∈ s, M i) *ᵥ v = ∑ i ∈ s, M i *ᵥ v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mulVec, ih]

theorem pow_card_eq (M : Matrix (Fin r) (Fin r) k) :
    M ^ r = - ∑ l ∈ Finset.range r, M.charpoly.coeff l • M ^ l := by
  have h0 := aeval_self_charpoly M
  rw [Polynomial.aeval_eq_sum_range, charpoly_natDegree_eq_dim, Fintype.card_fin,
    Finset.sum_range_succ] at h0
  have h1 : M.charpoly.coeff r = 1 := by
    have := (charpoly_monic M).leadingCoeff
    rwa [Polynomial.leadingCoeff, charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  rw [h1, one_smul] at h0
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h0

theorem companion_mulVec_ev (p : Fin r → k) (i : ℕ) (hi : i + 1 < r) :
    companion p *ᵥ ev r k i = ev r k (i + 1) := by
  rw [ev_eq_single i (by omega)]
  funext j
  simp only [mulVec_single, companion, of_apply, mul_one, ev]
  have : ¬ (i + 1 = r) := by omega
  simp [this]

theorem companion_mulVec_last (p : Fin r → k) (i : ℕ) (hi : i + 1 = r) :
    companion p *ᵥ ev r k i = - p := by
  rw [ev_eq_single i (by omega)]
  funext j
  simp [mulVec_single, companion, hi]

theorem companion_pow_ev (p : Fin r → k) (i : ℕ) (hi : i < r) :
    companion p ^ i *ᵥ ev r k 0 = ev r k i := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', ← mulVec_mulVec, ih (by omega), companion_mulVec_ev p i hi]

theorem companion_pow_card (p : Fin r → k) (hr : 0 < r) :
    companion p ^ r *ᵥ ev r k 0 = - p := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [pow_succ', ← mulVec_mulVec, companion_pow_ev p m (by omega), companion_mulVec_last p m rfl]

theorem charpoly_companion_coeff (p : Fin r → k) (i : Fin r) :
    (companion p).charpoly.coeff i = p i := by
  have hr : 0 < r := i.pos
  have h := pow_card_eq (companion p)
  have h2 := congrArg (fun M => M *ᵥ ev r k 0) h
  simp only [companion_pow_card p hr, neg_mulVec, sum_mulVec', smul_mulVec] at h2
  have h3 := congrFun h2 i
  simp only [Pi.neg_apply, neg_inj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3
  rw [h3, Finset.sum_eq_single (i : ℕ)]
  · simp [companion_pow_ev p i i.2, ev]
  · intro b hb hne
    rw [companion_pow_ev p b (Finset.mem_range.mp hb)]
    simp [ev, Ne.symm hne]
  · intro h; exact absurd (Finset.mem_range.mpr i.2) h

end GlobalTheory.JR.NormalFormL

namespace GlobalTheory.JR.NormalFormL

variable {k : Type} [Field k] {r : ℕ}

theorem inv_act' (g : GL (Fin r) k) (Y : Gl r k) : inv (act g Y) = inv Y := by
  obtain ⟨A, b, c, l⟩ := Y
  simp only [inv, act, mom, Prod.mk.injEq, and_true]
  refine ⟨?_, ?_⟩
  · funext i
    rw [Matrix.coe_units_inv, charpoly_units_conj]
  · funext i
    rw [Units.conj_pow, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
    congr 2
    simp [mul_assoc]

theorem act_mul' (g h : GL (Fin r) k) (Y : Gl r k) : act (g * h) Y = act g (act h Y) := by
  obtain ⟨A, b, c, l⟩ := Y
  simp only [act, _root_.mul_inv_rev, Units.val_mul, mulVec_mulVec, vecMul_vecMul, Prod.mk.injEq, and_true]
  try simp [mul_assoc]

theorem inv_sec' (a : Inv r k) : inv (sec a) = a := by
  obtain ⟨p, m, l⟩ := a
  simp only [inv, sec, Prod.mk.injEq, and_true]
  refine ⟨funext fun i => charpoly_companion_coeff p i, funext fun i => ?_⟩
  have he : (fun i : Fin r => if (i : ℕ) = 0 then (1 : k) else 0) = ev r k 0 := rfl
  simp only [mom, he, companion_pow_ev p i i.2, ev_eq_single (i : ℕ) i.2, dotProduct_single, mul_one]

theorem charpoly_companion_inv (Y : Gl r k) : (companion (inv Y).1).charpoly = Y.1.charpoly := by
  apply Polynomial.ext
  intro n
  rcases lt_trichotomy n r with h | h | h
  · exact charpoly_companion_coeff _ ⟨n, h⟩
  · subst h
    have h1 := (charpoly_monic (companion (inv Y).1)).leadingCoeff
    have h2 := (charpoly_monic Y.1).leadingCoeff
    rw [Polynomial.leadingCoeff, charpoly_natDegree_eq_dim, Fintype.card_fin] at h1 h2
    rw [h1, h2]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt] <;>
      simpa using h

theorem dot_pow_eq_sum (M : Matrix (Fin r) (Fin r) k) (hr : 0 < r) (b c : Fin r → k) (n : ℕ) :
    c ⬝ᵥ (M ^ n *ᵥ b) = ∑ i ∈ Finset.range r,
      ((Polynomial.X ^ n) %ₘ M.charpoly).coeff i * (c ⬝ᵥ (M ^ i *ᵥ b)) := by
  have hmon := charpoly_monic M
  have hdeg : M.charpoly.natDegree = r := by simp
  have hne : M.charpoly ≠ 1 := by
    intro h; rw [h, Polynomial.natDegree_one] at hdeg; omega
  have hM : M ^ n = Polynomial.aeval M ((Polynomial.X ^ n) %ₘ M.charpoly) := by
    rw [Polynomial.aeval_modByMonic_eq_self_of_root (aeval_self_charpoly M)]
    simp
  rw [hM, Polynomial.aeval_eq_sum_range' (n := r)
    (by have := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ n) hmon hne; omega), sum_mulVec', dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem mom_sec_inv (Y : Gl r k) (n : ℕ) : mom (sec (inv Y)) n = mom Y n := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp [mom, dotProduct]
  have hs := inv_sec' (inv Y)
  simp only [mom]
  rw [dot_pow_eq_sum _ hr, dot_pow_eq_sum _ hr]
  have hc : (sec (inv Y)).1.charpoly = Y.1.charpoly := charpoly_companion_inv Y
  rw [hc]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  have := congrFun (congrArg (fun a : Inv r k => a.2.1) hs) ⟨i, Finset.mem_range.mp hi⟩
  simpa [inv, mom] using this

theorem hankel_eq (Y : Gl r k) : Cm Y * Bm Y = hankel (inv Y) := by
  ext i j
  simp only [mul_apply, Cm, Bm, hankel, of_apply, mom_sec_inv]
  simp only [mom]
  rw [pow_add, ← mulVec_mulVec, dotProduct_mulVec]
  rfl

end GlobalTheory.JR.NormalFormL

namespace GlobalTheory.JR.NormalFormL

variable {k : Type} [Field k] {r : ℕ}

theorem mul_Bm (Y : Gl r k) : Y.1 * Bm Y = Bm Y * companion (inv Y).1 := by
  ext i j
  have hl : (Y.1 * Bm Y) i j = (Y.1 ^ ((j : ℕ) + 1) *ᵥ Y.2.1) i := by
    rw [pow_succ', ← mulVec_mulVec]
    simp [Matrix.mul_apply, Bm, mulVec, dotProduct]
  rw [hl, Matrix.mul_apply]
  by_cases hj : (j : ℕ) + 1 = r
  · simp only [companion, of_apply, hj, if_true, Bm, inv]
    rw [pow_card_eq Y.1, neg_mulVec, sum_mulVec']
    simp only [Pi.neg_apply, Finset.sum_apply, smul_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun l => (Y.1 ^ l *ᵥ Y.2.1) i * -Y.1.charpoly.coeff l),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  · have hj' : (j : ℕ) + 1 < r := by omega
    rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hj'⟩ : Fin r)]
    · simp [companion, hj, Bm]
    · intro l _ hne
      have : ¬ ((l : ℕ) = (j : ℕ) + 1) := fun h => hne (Fin.ext h)
      simp [companion, hj, this]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem vecMul_Bm (Y : Gl r k) : Y.2.2.1 ᵥ* Bm Y = (inv Y).2.1 := by
  funext j
  simp [vecMul, dotProduct, Bm, inv, mom, mulVec]

theorem det_Bm_ne (Y : Gl r k) (h : Delta (inv Y) ≠ 0) : (Bm Y).det ≠ 0 := by
  intro h0
  apply h
  rw [Delta, ← hankel_eq, det_mul, h0, mul_zero]

theorem unique_conj (Y Y₁ : Gl r k) (hΔ : Delta (inv Y) ≠ 0) (hI : inv Y₁ = inv Y) :
    ∃! g : GL (Fin r) k, act g Y = Y₁ ∧ (g : Matrix (Fin r) (Fin r) k) * Bm Y = Bm Y₁ := by
  have hB : IsUnit (Bm Y) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_Bm_ne Y hΔ))
  have hB₁ : IsUnit (Bm Y₁) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_Bm_ne Y₁ (hI ▸ hΔ)))
  set u := hB.unit with hu
  set u₁ := hB₁.unit with hu₁
  have eu : (u : Matrix (Fin r) (Fin r) k) = Bm Y := hB.unit_spec
  have eu₁ : (u₁ : Matrix (Fin r) (Fin r) k) = Bm Y₁ := hB₁.unit_spec
  refine ⟨u₁ * u⁻¹, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨A, b, c, l⟩ := Y
    obtain ⟨A₁, b₁, c₁, l₁⟩ := Y₁
    have hAB := mul_Bm (A, b, c, l)
    have hAB₁ := mul_Bm (A₁, b₁, c₁, l₁)
    have hc := vecMul_Bm (A, b, c, l)
    have hc₁ := vecMul_Bm (A₁, b₁, c₁, l₁)
    rw [hI] at hAB₁ hc₁
    rw [← eu] at hAB hc
    rw [← eu₁] at hAB₁ hc₁
    have hl : l₁ = l := congrArg (fun a : Inv r k => a.2.2) hI
    simp only [act, _root_.mul_inv_rev, inv_inv, Units.val_mul, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, hl.symm⟩
    · calc (u₁ : Matrix (Fin r) (Fin r) k) * ↑u⁻¹ * A * (↑u * ↑u₁⁻¹)
            = ↑u₁ * (↑u⁻¹ * (A * ↑u)) * ↑u₁⁻¹ := by simp only [mul_assoc]
          _ = ↑u₁ * companion (inv (A, b, c, l)).1 * ↑u₁⁻¹ := by
            rw [hAB, Units.inv_mul_cancel_left]
          _ = A₁ := by rw [← hAB₁, Units.mul_inv_cancel_right]
    · rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; funext i; exact i.elim0
      have e0 : ∀ (B : Matrix (Fin r) (Fin r) k) (Z : Gl r k), B = Bm Z →
          B *ᵥ Pi.single (⟨0, hr⟩ : Fin r) 1 = Z.2.1 := by
        intro B Z hBZ; subst hBZ; funext i; simp [mulVec_single, Bm, Function.swap]
      have hb : (u : Matrix (Fin r) (Fin r) k) *ᵥ Pi.single (⟨0, hr⟩ : Fin r) 1 = b :=
        e0 _ (A, b, c, l) eu
      have hb₁ : (u₁ : Matrix (Fin r) (Fin r) k) *ᵥ Pi.single (⟨0, hr⟩ : Fin r) 1 = b₁ :=
        e0 _ (A₁, b₁, c₁, l₁) eu₁
      rw [← hb, mulVec_mulVec, mul_assoc, Units.inv_mul, mul_one, hb₁]
    · have hc' : c ᵥ* (u : Matrix (Fin r) (Fin r) k) = c₁ ᵥ* (u₁ : Matrix (Fin r) (Fin r) k) :=
        hc.trans hc₁.symm
      rw [← vecMul_vecMul, hc', vecMul_vecMul, Units.mul_inv, vecMul_one]
  · rw [Units.val_mul, mul_assoc, eu.symm, Units.inv_mul, mul_one, eu₁]
  · rintro g ⟨_, hg⟩
    apply Units.ext
    rw [Units.val_mul, eu₁, ← hg, ← eu, mul_assoc, Units.mul_inv, mul_one]

end GlobalTheory.JR.NormalFormL

theorem GlobalTheory.JR.normalForm_invariants : ∀ (k : Type) [Field k] (r : ℕ), (∀ (g : GL (Fin r) k) (Y : Gl r k), inv (act g Y) = inv Y) ∧ (∀ a : Inv r k, inv (sec a) = a) ∧ (∀ Y : Gl r k, Cm Y * Bm Y = hankel (inv Y)) ∧ (∀ (g h : GL (Fin r) k) (Y : Gl r k), act (g * h) Y = act g (act h Y)) ∧ ∀ Y Y₁ : Gl r k, Delta (inv Y) ≠ 0 → inv Y₁ = inv Y → ∃! g : GL (Fin r) k, act g Y = Y₁ ∧ (g : Matrix (Fin r) (Fin r) k) * Bm Y = Bm Y₁ := by
  intro k _ r
  exact ⟨GlobalTheory.JR.NormalFormL.inv_act', GlobalTheory.JR.NormalFormL.inv_sec', GlobalTheory.JR.NormalFormL.hankel_eq,
    GlobalTheory.JR.NormalFormL.act_mul', GlobalTheory.JR.NormalFormL.unique_conj⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorKrylovDet
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.TransferFactor

variable {k : Type} [CommRing k] {r : ℕ}

theorem full_cc (Y : Gl r k) (a b : Fin r) : full Y (Fin.castSucc a) (Fin.castSucc b) = Y.1 a b := by
  simp [full, finSumFinEquiv_symm_apply_castSucc]

theorem full_lc (Y : Gl r k) (b : Fin r) : full Y (Fin.last r) (Fin.castSucc b) = Y.2.2.1 b := by
  simp [full, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

def vrow (Y : Gl r k) (i : ℕ) : Fin (r + 1) → k := Pi.single (Fin.last r) (1 : k) ᵥ* (full Y ^ i)

theorem vrow_succ_cast (Y : Gl r k) (i : ℕ) (j : Fin r) :
    vrow Y (i + 1) (Fin.castSucc j) =
      ((fun l => vrow Y i (Fin.castSucc l)) ᵥ* Y.1) j + vrow Y i (Fin.last r) * Y.2.2.1 j := by
  simp only [vrow, pow_succ, ← Matrix.vecMul_vecMul]
  rw [Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc]
  simp only [full_cc, full_lc]
  rfl

theorem vrow_poly (Y : Gl r k) (i : ℕ) : ∃ p : Polynomial k, p.coeff i = 1 ∧ (∀ N, i < N → p.coeff N = 0) ∧
    (fun l => vrow Y (i + 1) (Fin.castSucc l)) = Y.2.2.1 ᵥ* Polynomial.aeval Y.1 p := by
  induction i with
  | zero =>
    refine ⟨1, by simp, fun N hN => ?_, ?_⟩
    · rw [Polynomial.coeff_one]; simp; omega
    · funext l
      rw [vrow_succ_cast]
      simp [vrow, Pi.single_apply, Fin.castSucc_ne_last, Matrix.vecMul, dotProduct, Matrix.one_apply_ne' (Fin.castSucc_ne_last _), Matrix.one_apply]
  | succ i ih =>
    obtain ⟨p, h1, h2, h3⟩ := ih
    refine ⟨p * Polynomial.X + Polynomial.C (vrow Y (i + 1) (Fin.last r)), ?_, fun N hN => ?_, ?_⟩
    · rw [Polynomial.coeff_add, Polynomial.coeff_mul_X, Polynomial.coeff_C, h1]; simp
    · rw [Polynomial.coeff_add, Polynomial.coeff_C]
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      rw [Polynomial.coeff_mul_X, h2 M (by omega)]; simp
    · funext l
      rw [vrow_succ_cast, h3]
      simp [map_add (f := _), Polynomial.aeval_X, Polynomial.aeval_C, Matrix.vecMul_add, Matrix.vecMul_vecMul,
        Algebra.algebraMap_eq_smul_one, Matrix.vecMul_smul, mul_comm]

theorem lastDet_eq (Y : Gl r k) : lastDet Y = (-1) ^ r * (Cm Y).det := by
  classical
  choose p hp1 hp2 hp3 using vrow_poly Y
  let T : Matrix (Fin r) (Fin r) k := Matrix.of fun i j => (p i).coeff j
  have hT : T.det = 1 := by
    rw [Matrix.det_of_lowerTriangular T (fun i j hij => hp2 i j hij)]
    exact Finset.prod_eq_one fun i _ => hp1 i
  have hmin : (Matrix.of fun (i j : Fin r) => vrow Y ((i : ℕ) + 1) (Fin.castSucc j)) = T * Cm Y := by
    ext i j
    have hd : (p i).natDegree < r := lt_of_le_of_lt
      (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (hp2 i)) i.2
    rw [Matrix.of_apply, congrFun (hp3 i) j, Polynomial.aeval_eq_sum_range' hd, Finset.sum_range
      (fun l => (p i).coeff l • Y.1 ^ l), Matrix.vecMul_sum]
    simp [Matrix.mul_apply, T, Cm, Matrix.vecMul_smul, Finset.sum_apply, mul_comm]
  unfold lastDet
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_castSucc]
  have hz : ∀ j : Fin r, (Matrix.of fun (i j : Fin (r + 1)) =>
      (Pi.single (Fin.last r) (1 : k) ᵥ* (full Y ^ (i : ℕ))) j) 0 (Fin.castSucc j) = 0 := by
    intro j; simp [Pi.single_apply, Fin.castSucc_ne_last, Matrix.one_apply_ne' (Fin.castSucc_ne_last _)]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  rw [show (Matrix.of fun (i j : Fin (r + 1)) =>
      (Pi.single (Fin.last r) (1 : k) ᵥ* (full Y ^ (i : ℕ))) j) 0 (Fin.last r) = 1 by simp]
  rw [Fin.succAbove_last]
  have hs : ((Matrix.of fun (i j : Fin (r + 1)) =>
      (Pi.single (Fin.last r) (1 : k) ᵥ* (full Y ^ (i : ℕ))) j).submatrix Fin.succ Fin.castSucc) =
      Matrix.of fun (i j : Fin r) => vrow Y ((i : ℕ) + 1) (Fin.castSucc j) := by
    ext i j; simp [vrow]
  rw [hs, hmin, Matrix.det_mul, hT, Fin.val_last]; ring

theorem Cm_act (g : GL (Fin r) k) (Y : Gl r k) :
    Cm (act g Y) = Cm Y * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  ext i j
  simp only [Cm, act, Matrix.of_apply, Units.conj_pow, Matrix.mul_apply]
  rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_vecMul _ _ (g : Matrix (Fin r) (Fin r) k)]
  rw [show ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * (g : Matrix (Fin r) (Fin r) k) = 1 from
    Units.inv_mul g, Matrix.vecMul_one]
  simp [Matrix.vecMul, dotProduct, Cm]

end GlobalTheory.JR.TransferFactor

theorem GlobalTheory.JR.transfer_factor_lemma : ∀ (k : Type) [CommRing k] (r : ℕ), (∀ Y : Gl r k, lastDet Y = (-1) ^ r * (Cm Y).det) ∧ ∀ (g : GL (Fin r) k) (Y : Gl r k), Cm (act g Y) = Cm Y * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) :=
  fun _ _ _ => ⟨GlobalTheory.JR.TransferFactor.lastDet_eq, GlobalTheory.JR.TransferFactor.Cm_act⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KappaSumZeroAndStableSumMulZeroOfNotIntegral
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma


open Polynomial in
theorem _root_.GlobalTheory.UnitLemma.isIntegral_of_isLat_stable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A]
    [Algebra E A] (L : Submodule O A) (hL : _root_.GlobalTheory.UnitLemma.IsLat O E L) (g : A) (hg : ∀ y ∈ L, g * y ∈ L) :
    IsIntegral O g := by
  obtain ⟨hfg, hspan⟩ := hL
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hfg
  let f : Module.End O L := (LinearMap.mulLeft O g).restrict hg
  have hpow : ∀ (n : ℕ) (y : L), ((f ^ n) y : A) = g ^ n * y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih => intro y; rw [pow_succ', Module.End.mul_apply, pow_succ', mul_assoc, ← ih]; rfl
  have hact : ∀ (q : O[X]) (y : L), ((aeval f q) y : A) = aeval g q * y := by
    intro q y
    induction q using Polynomial.induction_on' with
    | add p q hp' hq' => simp [add_mul, hp', hq']
    | monomial n c => simp [aeval_monomial, hpow, Algebra.smul_def, mul_assoc]
  obtain ⟨p, hmon, hp⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  have hzero : ∀ y ∈ Submodule.span E (L : Set A), aeval g p * y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => rw [← hact p ⟨x, hx⟩, hp]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul e x _ hx => rw [mul_smul_comm, hx, smul_zero]
  refine ⟨p, hmon, ?_⟩
  have h1 := hzero 1 (hspan ▸ Submodule.mem_top)
  rw [mul_one] at h1
  rwa [← aeval_def]

open Polynomial in
private lemma latticeCount_eq_zero_of_not_isIntegral_lemma (K : _root_.GlobalTheory.UnitLemma.UQ)
    (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (hB : ¬ IsIntegral K.O B.g) (k : B.Cl) :
    B.N k.rep = 0 := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.N _root_.GlobalTheory.UnitLemma.orbSum _root_.GlobalTheory.UnitLemma.InvAlg.X
  refine finsum_eq_zero_of_forall_eq_zero fun o => absurd ?_ hB
  obtain ⟨hfull, hstab, -⟩ := (Quot.out o).2
  exact _root_.GlobalTheory.UnitLemma.isIntegral_of_isLat_stable _ hfull _ hstab

open Polynomial in
private lemma stableLatticeCountSum_eq_zero_of_not_isIntegral_lemma_2 (K : _root_.GlobalTheory.UnitLemma.UQ)
    (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (hB : ¬ IsIntegral K.O B.g) :
    B.stSum = 0 := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.stSum
  exact finsum_eq_zero_of_forall_eq_zero fun k => latticeCount_eq_zero_of_not_isIntegral_lemma K B hB k


open Polynomial in
theorem _root_.GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral :
    ∀ (K : _root_.GlobalTheory.UnitLemma.UQ) (B₁ B₂ : _root_.GlobalTheory.UnitLemma.InvAlg K),
      ¬ (IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g) →
      _root_.GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ = 0 ∧
        B₁.stSum * B₂.stSum = 0 := by
  intro K B₁ B₂ h
  have hprod : ¬ IsIntegral K.O (B₁.prod B₂).g := by
    intro hi
    have hi' : IsIntegral K.O ((B₁.g, B₂.g) : B₁.A × B₂.A) := hi
    apply h
    exact ⟨hi'.map (AlgHom.fst K.O B₁.A B₂.A), hi'.map (AlgHom.snd K.O B₁.A B₂.A)⟩
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.UnitLemma.InvAlg.kapSum
    refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
    rw [latticeCount_eq_zero_of_not_isIntegral_lemma K _ hprod k, mul_zero]
  · by_cases h₁ : IsIntegral K.O B₁.g
    · rw [stableLatticeCountSum_eq_zero_of_not_isIntegral_lemma_2 K B₂ fun h₂ => h ⟨h₁, h₂⟩, mul_zero]
    · rw [stableLatticeCountSum_eq_zero_of_not_isIntegral_lemma_2 K B₁ h₁, zero_mul]

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixNearOnePowPrimeDeep
section
namespace GlobalTheory

theorem matrix_near_one_pow_prime_deep : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n]
    (X : Matrix n n ℚ_[l]) (k : ℕ), (∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-2 : ℤ)) →
    (∀ i j, ‖(X ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2))) →
    ∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
  intro l hl n _ _ X k h1 h2 i j
  have hL : (2:ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hLpos : (0:ℝ) < l := by linarith
  set u : ℝ := (l:ℝ)⁻¹ with hu
  have u0 : 0 < u := inv_pos.mpr hLpos
  have uhalf : u ≤ 1 / 2 := by
    rw [hu, one_div]; exact inv_anti₀ (by norm_num) hL
  have hz : ∀ m : ℕ, (l:ℝ) ^ (-(m:ℤ)) = u ^ m := fun m => by
    rw [zpow_neg, zpow_natCast, inv_pow]
  have e2 : (l:ℝ) ^ (-2:ℤ) = u ^ 2 := hz 2
  have e3 : (l:ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) = u ^ (k + 3) := by
    rw [← hz]; congr 1
  have e4 : (l:ℝ) ^ (-((k : ℤ) + 2)) = u ^ (k + 2) := by
    rw [← hz]; congr 1
  rw [e4]
  set Y := X - 1 with hY
  haveI : Nonempty (n × n) := ⟨(i, j)⟩
  obtain ⟨⟨i0, j0⟩, hmax⟩ := Finite.exists_max (fun p : n × n => ‖Y p.1 p.2‖)
  set t := ‖Y i0 j0‖ with ht
  have hall : ∀ a b, ‖Y a b‖ ≤ t := fun a b => hmax (a, b)
  suffices hs : t ≤ u ^ (k + 2) from (hall i j).trans hs
  have t0 : 0 ≤ t := norm_nonneg _
  have tsmall : t ≤ u ^ 2 := e2 ▸ h1 i0 j0
  have u1 : u ≤ 1 := by linarith
  have t1 : t ≤ 1 := tsmall.trans (pow_le_one₀ u0.le u1)
  have hR := _root_.GlobalTheory.matrix_one_add_pow_sub_entry_le ℚ_[l] n Y t t0 t1 hall l i0 j0
  have hX : (1 + Y) = X := by rw [hY]; abel
  rw [hX] at hR
  have key : ‖((l:ℚ_[l]) • Y) i0 j0‖ ≤ max (‖(X ^ l - 1) i0 j0‖) (t ^ 2) := by
    have : ((l:ℚ_[l]) • Y) i0 j0 = (X ^ l - 1) i0 j0 - (X ^ l - 1 - (l:ℚ_[l]) • Y) i0 j0 := by
      simp [Matrix.sub_apply]
    rw [this]
    have hu' : ∀ a b : ℚ_[l], ‖a - b‖ ≤ max ‖a‖ ‖b‖ := fun a b => by
      rw [sub_eq_add_neg, ← norm_neg b]; exact IsUltrametricDist.norm_add_le_max _ _
    exact (hu' _ _).trans (max_le_max le_rfl hR)
  have hnorm : ‖((l:ℚ_[l]) • Y) i0 j0‖ = u * t := by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Padic.norm_p]
  rw [hnorm] at key
  rcases le_max_iff.mp key with h | h
  · have h' : u * t ≤ u * u ^ (k + 2) := by
      rw [← pow_succ', ← e3]; exact h.trans (h2 i0 j0)
    exact le_of_mul_le_mul_left h' u0
  · rcases t0.eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · exfalso
      have : u ≤ t := by nlinarith
      nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanImageSemilinearLatticeEqStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_image_semilinear_lattice_eq : ∀ (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module (FractionRing O) V'] [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V'), (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) → ∀ S : Set V, Submodule.span O (iV '' (Submodule.span (𝓞 K) S : Set V)) = Submodule.span O (iV '' S) := by
  first | exact @GlobalTheory.span_image_span_eq_of_integral | exact GlobalTheory.span_image_span_eq_of_integral | (intros; apply GlobalTheory.span_image_span_eq_of_integral <;> assumption)
end

