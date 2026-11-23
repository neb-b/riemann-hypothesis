module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FourTermExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CvRhoOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040

@[expose] public section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem gv_inv {y : Mat k r} (hy : y ∈ GV k r) : y * y⁻¹ = 1 ∧ y⁻¹ * y = 1 := by
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have hl : (Hpk k r * yᴴ * Hpk k r) * y = 1 := by
    calc (Hpk k r * yᴴ * Hpk k r) * y = Hpk k r * (yᴴ * Hpk k r * y) := by simp only [mul_assoc]
      _ = 1 := by rw [hy', Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  have hdet : IsUnit y.det := Matrix.isUnit_det_of_left_inverse hl
  exact ⟨Matrix.mul_nonsing_inv y hdet, Matrix.nonsing_inv_mul y hdet⟩

theorem loc_finsum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Φ : ι → Mat k r → E) {m : ℕ∞} {g : Mat k r}
    (h : ∀ i ∈ s, Loc m (Φ i) g) : Loc m (fun z => ∑ i ∈ s, c i • Φ i z) g := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    exact loc_of_eq (by funext z; simp) (loc_zero m g)
  · intro j s hj ih h
    exact loc_of_eq (by funext z; rw [Finset.sum_insert hj, add_comm])
      (loc_add (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) (h j (Finset.mem_insert_self j s)) (c j))

theorem top_finsum (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (Φ : ι → Mat k r → E) {g : Mat k r} (hg : g ∈ GV k r) (h : ∀ i ∈ s, Loc 1 (Φ i) g)
    (v : ℂ) (a b : Fin (2 * r + k + 1)) :
    Top (FourTermExpansion.LT M) v a b (fun z => ∑ i ∈ s, c i • Φ i z) g = ∑ i ∈ s, c i • Top (FourTermExpansion.LT M) v a b (Φ i) g := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [FourTermExpansion.top_apply'', FourTermExpansion.EZ_zero]
  · intro j s hj ih h
    have hs : ∀ i ∈ s, Loc 1 (Φ i) g := fun i hi => h i (Finset.mem_insert_of_mem hi)
    calc Top (FourTermExpansion.LT M) v a b (fun z => ∑ i ∈ insert j s, c i • Φ i z) g
        = Top (FourTermExpansion.LT M) v a b (fun z => (∑ i ∈ s, c i • Φ i z) + c j • Φ j z) g := by
          congr 1; funext z; rw [Finset.sum_insert hj, add_comm]
      _ = Top (FourTermExpansion.LT M) v a b (fun z => ∑ i ∈ s, c i • Φ i z) g + c j • Top (FourTermExpansion.LT M) v a b (Φ j) g :=
          FourTermExpansion.top_lin M (loc_finsum s c Φ hs) (h j (Finset.mem_insert_self j s)) hg (c j) v a b
      _ = _ := by rw [ih hs, Finset.sum_insert hj, add_comm]

def Mc (y : Mat k r) (a b : Fin (2 * r + k + 1)) : Mat k r := y⁻¹ * Msg k r a b * y

private theorem Hpk_inv_conjTranspose_conj_eq_conj_of_mem_GV {y : Mat k r} (hy : y ∈ GV k r) (Z : Mat k r) :
    (Hpk k r)⁻¹ * (y⁻¹ * Z * y)ᴴ * Hpk k r = y⁻¹ * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) * y := by
  have hHH : Hpk k r * Hpk k r = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hHH' : ∀ A : Mat k r, Hpk k r * (Hpk k r * A) = A := fun A => by rw [← mul_assoc, hHH, one_mul]
  have hinvH : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hHH
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have hinv : y⁻¹ = Hpk k r * yᴴ * Hpk k r := by
    apply Matrix.inv_eq_left_inv
    simp only [mul_assoc] at hy' ⊢
    rw [hy', hHH]
  rw [hinvH, hinv]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.QuantumDeterminants.GBasic.Hpk_herm, mul_assoc,
    hHH, mul_one, hHH']

private theorem hermitian_half_one_conj_of_mem_GV {y : Mat k r} (hy : y ∈ GV k r) (Z : Mat k r) :
    hpart1 (Hpk k r) (y⁻¹ * Z * y) = y⁻¹ * hpart1 (Hpk k r) Z * y := by
  unfold hpart1
  rw [Hpk_inv_conjTranspose_conj_eq_conj_of_mem_GV hy, Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul]

private theorem hermitian_half_two_conj_of_mem_GV {y : Mat k r} (hy : y ∈ GV k r) (Z : Mat k r) :
    hpart2 (Hpk k r) (y⁻¹ * Z * y) = y⁻¹ * hpart2 (Hpk k r) Z * y := by
  unfold hpart2
  rw [Hpk_inv_conjTranspose_conj_eq_conj_of_mem_GV hy, Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul]

theorem EHc_eq_LT (y : Mat k r) (hy : y ∈ GV k r) :
    Formalism.FourierDecayAlt.P.JFxB.EHc (E := E) k r y = FourTermExpansion.LT (Mc y) := by
  funext c d f g
  show RdV (y⁻¹ * hpart1 (Hpk k r) (Matrix.single c d 1) * y) f g +
      Complex.I • RdV (y⁻¹ * hpart2 (Hpk k r) (Matrix.single c d 1) * y) f g =
    RdV (hpart1 (Hpk k r) (y⁻¹ * Matrix.single c d 1 * y)) f g +
      Complex.I • RdV (hpart2 (Hpk k r) (y⁻¹ * Matrix.single c d 1 * y)) f g
  rw [hermitian_half_one_conj_of_mem_GV hy, hermitian_half_two_conj_of_mem_GV hy]

theorem Mc_expand (y : Mat k r) (a b : Fin (2 * r + k + 1)) :
    Mc y a b = ∑ ab : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
      ((y⁻¹) ab.1 a * y b ab.2) • Msg k r ab.1 ab.2 := by
  ext i j
  simp [Mc, Msg, Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, Fintype.sum_prod_type, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem conv (y : Mat k r) (hy : y ∈ GV k r) {Ψ : Mat k r → E} {g : Mat k r} (hΨ : Loc 1 Ψ g)
    (hg : g ∈ GV k r) (v : ℂ) (a b : Fin (2 * r + k + 1)) :
    Top (FourTermExpansion.LT (Mc y)) v a b Ψ g = ∑ ab : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
      ((y⁻¹) ab.1 a * y b ab.2) • Top (FourTermExpansion.LT (Msg k r)) v ab.1 ab.2 Ψ g := by
  have hsum : ∑ ab : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
      ((y⁻¹) ab.1 a * y b ab.2) • (if ab.1 = ab.2 then v • Ψ g else 0) = if a = b then v • Ψ g else 0 := by
    have h1 : ∀ ab : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
        ((y⁻¹) ab.1 a * y b ab.2) • (if ab.1 = ab.2 then v • Ψ g else (0 : E)) =
          (if ab.1 = ab.2 then (y⁻¹) ab.1 a * y b ab.2 else 0) • (v • Ψ g) := fun ab => by
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun ab _ => h1 ab), ← Finset.sum_smul]
    have h2 : ∑ ab : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
        (if ab.1 = ab.2 then (y⁻¹) ab.1 a * y b ab.2 else 0) = if a = b then 1 else 0 := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have := congrFun (congrFun (gv_inv hy).1 b) a
      rw [Matrix.mul_apply] at this
      rw [Finset.sum_congr rfl (fun p _ => mul_comm _ _), this, Matrix.one_apply]
      simp only [eq_comm]
    rw [h2]
    split_ifs <;> simp
  rw [FourTermExpansion.top_apply'' (Mc y), Mc_expand y a b, EZ_sum hΨ hg]
  simp only [FourTermExpansion.top_apply'', smul_add, Finset.sum_add_distrib, hsum]

end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem sum_fun_succ {α M : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid M] {t : ℕ}
    (G : (Fin (t + 1) → α) → M) :
    ∑ C : Fin (t + 1) → α, G C = ∑ a : α, ∑ c : Fin t → α, G (Fin.cons a c) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => α) _ _ fun p => rfl).symm

theorem expandM (y : Mat k r) (hy : y ∈ GV k r) : ∀ (t : ℕ) (f : Fin t → ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))
    (Φ : Mat k r → E) (x : Mat k r), x ∈ GV k r → Loc (t : ℕ∞) Φ x →
    fold (Mc y) (List.ofFn f) Φ x = ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1),
      (∏ j, ((y⁻¹) (c j) (f j).2.1 * y (f j).2.2 (d j))) •
        fold (Msg k r) (List.ofFn fun j => ((f j).1, c j, d j)) Φ x := by
  intro t
  induction t with
  | zero =>
    intro f Φ x _ _
    simp [FourTermExpansion.fold_nil]
  | succ t ih =>
    intro f Φ x hx hloc
    obtain ⟨U, hU, hxU, hUl⟩ := loc_spread hloc
    have hle : ((t : ℕ) : ℕ∞) ≤ ((t + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_succ t
    have heq : ∀ z ∈ U, z ∈ GV k r → fold (Mc y) (List.ofFn fun j : Fin t => f j.succ) Φ z =
        (fun z => ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1),
          (∏ j, ((y⁻¹) (c j) (f j.succ).2.1 * y (f j.succ).2.2 (d j))) •
            fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) z :=
      fun z hz hzG => ih (fun j => f j.succ) Φ z hzG (loc_mono hle (hUl z hz))
    have e1 : 1 + t = t + 1 := by omega
    have hF : ∀ c d : Fin t → Fin (2 * r + k + 1),
        Loc 1 (fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ) x := by
      intro c d
      have := FourTermExpansion.fold_loc (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) 1 Φ x
        (by rw [List.length_ofFn, e1]; exact hloc)
      simpa using this
    have hin : ∀ (G : (Fin t → Fin (2 * r + k + 1)) → (Fin t → Fin (2 * r + k + 1)) → ℂ)
        (c : Fin t → Fin (2 * r + k + 1)),
        Loc 1 (fun z => ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
          fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) x :=
      fun G c => loc_finsum _ _ _ (fun d _ => hF c d)
    have hΨ : ∀ G : (Fin t → Fin (2 * r + k + 1)) → (Fin t → Fin (2 * r + k + 1)) → ℂ,
        Loc 1 (fun z => ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
          fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) x := fun G =>
      loc_of_eq (by funext z; simp)
        (loc_finsum Finset.univ (fun _ => (1 : ℂ)) (fun c z => ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
          fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) (fun c _ => hin G c))
    have hT : ∀ (G : (Fin t → Fin (2 * r + k + 1)) → (Fin t → Fin (2 * r + k + 1)) → ℂ) (v : ℂ)
        (a b : Fin (2 * r + k + 1)),
        Top (FourTermExpansion.LT (Msg k r)) v a b (fun z => ∑ c : Fin t → Fin (2 * r + k + 1),
          ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
            fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) x =
        ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
          Top (FourTermExpansion.LT (Msg k r)) v a b (fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ) x := by
      intro G v a b
      have e : (fun z => ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
          fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) =
          fun z => ∑ c ∈ Finset.univ, (1 : ℂ) • (fun c z => ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
            fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) c z := by
        funext z; simp
      rw [e, top_finsum (Msg k r) Finset.univ _ _ hx (fun c _ => hin G c)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [one_smul, top_finsum (Msg k r) Finset.univ _ _ hx (fun d _ => hF c d)]
    rw [List.ofFn_succ, FourTermExpansion.fold_cons, FourTermExpansion.top_congr (Mc y) hU heq _ _ _ x hxU hx, conv y hy (hΨ _) hx]
    simp only [hT, sum_fun_succ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ, FourTermExpansion.fold_cons,
      Finset.smul_sum, smul_smul, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]

end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem skewRow {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (Φ : Mat k r → E) (g : Mat k r)
    (τ : Equiv.Perm (Fin t)) :
    qminorOp (Q.EH k r) (a ∘ τ) b u Φ g = ((Equiv.Perm.sign τ : ℤ) : ℂ) • qminorOp (Q.EH k r) a b u Φ g := by
  have hτ : ((Equiv.Perm.sign τ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  rw [FourTermExpansion.qm_eq, FourTermExpansion.qm_eq, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => ?_)
  show ((Equiv.Perm.sign σ : ℤ) : ℂ) • FourTermExpansion.PP a b u (τ * σ) Φ g = _
  simp only [Equiv.coe_mulLeft, smul_smul, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, ← mul_assoc, hτ,
    one_mul]

theorem row_zero {t : ℕ} (c b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (Φ : Mat k r → E) (g : Mat k r)
    (hc : ¬ Function.Injective c) : qminorOp (Q.EH k r) c b u Φ g = 0 := by
  unfold Function.Injective at hc
  push_neg at hc
  obtain ⟨i, j, hij, hne⟩ := hc
  have hcτ : c ∘ Equiv.swap i j = c := by
    funext x
    simp only [Function.comp_apply]
    rcases eq_or_ne x i with rfl | hxi
    · simp [hij]
    rcases eq_or_ne x j with rfl | hxj
    · simp [hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
  have := skewRow c b u Φ g (Equiv.swap i j)
  rw [hcτ, Equiv.Perm.sign_swap hne] at this
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul] at this
  have h2 := sub_eq_zero.mpr this
  rw [sub_neg_eq_add] at h2
  exact FourTermExpansion.half _ h2

theorem col_zero {t : ℕ} (a d : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (Φ : Mat k r → E) (g : Mat k r)
    (hg : g ∈ GV k r) (hloc : Loc (t : ℕ∞) Φ g) (hd : ¬ Function.Injective d) :
    qminorOp (Q.EH k r) a d u Φ g = 0 := by
  unfold Function.Injective at hd
  push_neg at hd
  obtain ⟨i, j, hij, hne⟩ := hd
  have hdτ : d ∘ Equiv.swap i j = d := by
    funext x
    simp only [Function.comp_apply]
    rcases eq_or_ne x i with rfl | hxi
    · simp [hij]
    rcases eq_or_ne x j with rfl | hxj
    · simp [hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
  have := FourTermExpansion.skewCol a u Φ g hg hloc d (Equiv.swap i j)
  rw [hdτ, Equiv.Perm.sign_swap hne] at this
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul] at this
  have h2 := sub_eq_zero.mpr this
  rw [sub_neg_eq_add] at h2
  exact FourTermExpansion.half _ h2

end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
