module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.RepresentsTransferOneOne
section
open Matrix Finset MeasureTheory
open scoped ContDiff

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}

theorem repTm (H : Hyp k r z z' i μ) (w : ℂ) (a b : Fin (mdim k r i)) :
    RepOn (hI H) (Tm (EA H) w a b) (Top (EH k r) w (posL k r i a) (posL k r i b)) := by
  have h := repOn_add (hI H) (repOn_ite (hI H) (a = b) (repOn_algebraMap (hI H) w) (repOn_zero (hI H)))
    (repE H a b)
  unfold Tm
  refine repOn_of_eq h fun f => ?_
  funext g
  by_cases hab : a = b
  · subst hab; simp [Formalism.QuantumDeterminants.Top, EOp]
  · have : posL k r i a ≠ posL k r i b := fun h => hab (posL_inj h)
    simp [Formalism.QuantumDeterminants.Top, EOp, hab, this]

theorem repQminor (H : Hyp k r z z' i μ) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (w : ℂ) :
    RepOn (hI H) (qminor (EA H) a b w) (qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) w) := by
  unfold qminor
  exact repOn_sum (hI H) Finset.univ fun σ _ => repOn_mul (hI H) (repOn_intCast (hI H) _)
    (repOn_list (hI H) t _ _ fun k' => repTm H _ _ _)

theorem represents_transfer_zero_zero (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 0 0)
      (tL k r z z' i Y 0 0) :=
  repQminor H id id _

theorem represents_transfer_zero_one (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 0 1)
      (tL k r z z' i Y 0 1) := by
  have h := repOn_neg (hI H) (repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun a _ => repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun b _ =>
    repOn_smul (hI H) ((-1 : ℂ) ^ ((a : ℕ) + (b : ℕ)) * xv k r z' i b)
      (repOn_mul (hI H) (repYb H a) (repQminor H (skip1 a) (skip1 b) (uC k r i Y - 1))))
  refine repOn_of_eq h fun f => ?_
  funext g
  simp only [tL, chatL, MOp, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

theorem represents_transfer_one_zero (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 1 0)
      (tL k r z z' i Y 1 0) := by
  have h := repOn_neg (hI H) (repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun a _ => repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun b _ =>
    repOn_smul (hI H) ((-1 : ℂ) ^ ((a : ℕ) + (b : ℕ)) * xbv k r z' i a)
      (repOn_mul (hI H) (repY H b) (repQminor H (skip1 a) (skip1 b) (uC k r i Y))))
  refine repOn_of_eq h fun f => ?_
  funext g
  simp only [tL, chatL, MOp, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

theorem tA_11 {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Y Yb : Fin m → A)
    (x xb : Fin m → ℂ) (u : ℂ) : tA E Y Yb x xb u 1 1 = -∑ i : Fin m, ∑ i' : Fin m, ∑ j : Fin m, ∑ j' : Fin m,
      if i < i' ∧ j < j' then
        ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ))) •
          ((Yb i * algebraMap ℂ A (xb i') - Yb i' * algebraMap ℂ A (xb i)) *
            (Y j * algebraMap ℂ A (x j') - Y j' * algebraMap ℂ A (x j)) *
            qminor E (skip2 i i') (skip2 j j') (u - 1))
      else 0 := rfl

theorem represents_transfer_one_one (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 1 1)
      (tL k r z z' i Y 1 1) := by
  have h := repOn_neg (hI H) (repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun a _ => repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun a' _ =>
    repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun b _ => repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun b' _ =>
    repOn_ite (hI H) (a < a' ∧ b < b')
      (repOn_smul (hI H) ((-1 : ℂ) ^ ((a : ℕ) + (a' : ℕ) + (b : ℕ) + (b' : ℕ)))
        (repOn_mul (hI H)
          (repOn_mul (hI H)
            (repOn_sub (hI H) (repOn_mul (hI H) (repYb H a) (repOn_algebraMap (hI H) (xbv k r z' i a')))
              (repOn_mul (hI H) (repYb H a') (repOn_algebraMap (hI H) (xbv k r z' i a))))
            (repOn_sub (hI H) (repOn_mul (hI H) (repY H b) (repOn_algebraMap (hI H) (xv k r z' i b')))
              (repOn_mul (hI H) (repY H b') (repOn_algebraMap (hI H) (xv k r z' i b)))))
          (repQminor H (skip2 a a') (skip2 b b') (uC k r i Y - 1))))
      (repOn_zero (hI H)))
  rw [tA_11]
  refine repOn_of_eq h fun f => ?_
  funext g
  simp only [tL, chat2L, Pi.neg_apply, Finset.sum_apply]
  rw [neg_inj]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro a' _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro b' _
  split_ifs
  · simp only [MOp, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  · rfl

theorem rep_tL (H : Hyp k r z z' i μ) (Y : ℂ) (p q : Fin 2) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) p q)
      (tL k r z z' i Y p q) := by
  fin_cases p <;> fin_cases q
  · exact represents_transfer_zero_zero H Y
  · exact represents_transfer_zero_one H Y
  · exact represents_transfer_one_zero H Y
  · exact represents_transfer_one_one H Y

theorem uC_star (Y : ℂ) : star (uC k r i Y) = uC k r i (star Y) := by
  simp [uC]

theorem glue_holds_var : Glue := by
  intro hAlg hET hEA hMT hTI hYb hXb hHm hEP hGl hYL k r z z' i μ hμ hz hz' f₁ f₂ hs₁ hs₂ hc₁ hc₂ Y a b
  have H : Hyp k r z z' i μ := ⟨hμ, hz, hz', hET, hEA, hMT, hTI, hYb, hXb, hHm, hEP, hGl, hYL⟩
  have hstar := hAlg (A (hI H)) (mdim k r i) (EA H) (YA H) (YbA H) (Hm k r i) (xv k r z' i) (xbv k r z' i)
    (glRel_A H) (hHm k r i).1 (hHm k r i).2 (starE_A H) (yComm H) (ybComm H) (yybComm H) (eyComm H) (eybComm H)
    (ybStar H) (hXb k r z' i hz') (uC k r i Y) a b
  have hT := rep_tL H Y a b
  have hS : RepOn (hI H) (star (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) a b))
      (tL k r z z' i (star Y) b a) := by
    rw [hstar, uC_star]
    exact rep_tL H (star Y) b a
  exact pr_of_repOn (hI H) hT hS (mem_testSub.2 ⟨hs₁, hc₁⟩) (mem_testSub.2 ⟨hs₂, hc₂⟩)

end PI.QnHermHaar
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.SumFourCommVersion
section
open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem commSumA {A : Type*} [Ring A] {ι : Type*} [Fintype ι] (h : ι → A) (g : A) :
    (∑ i, h i) * g - g * (∑ i, h i) = ∑ i, (h i * g - g * h i) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem commSumB {A : Type*} [Ring A] {ι : Type*} [Fintype ι] (h : ι → A) (g : A) :
    g * (∑ i, h i) - (∑ i, h i) * g = ∑ i, (g * h i - h i * g) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem smulComm {A : Type*} [Ring A] [Algebra ℂ A] (α β : ℂ) (X Y : A) :
    (α • X) * (β • Y) - (β • Y) * (α • X) = (α * β) • (X * Y - Y * X) := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm β α, smul_sub]

def vecC {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℂ) (Y : Fin m → A) : Fin m → A :=
  fun c => ∑ k, Q c k • Y k

def covC {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (Yb : Fin m → A) : Fin m → A :=
  fun c => ∑ l, P l c • Yb l

theorem qpApply {m : ℕ} (P Q : Matrix (Fin m) (Fin m) ℂ) (hQP : Q * P = 1) (b c : Fin m) :
    ∑ j, Q b j * P j c = if b = c then 1 else 0 := by
  have h := congrFun (congrFun hQP b) c
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  exact h

theorem glConj {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A)
    (P Q : Matrix (Fin m) (Fin m) ℂ) (hGl : GlRel E) (hQP : Q * P = 1) : GlRel (Econj E P Q) := by
  intro a b c d
  have hG : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0) := hGl
  simp only [Econj]
  simp_rw [commSumA]
  simp_rw [commSumB]
  simp only [smulComm, hG, smul_sub, Finset.sum_sub_distrib, smul_ite, smul_zero]
  congr 1
  ·
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
    simp only [← Finset.sum_smul]
    have hc : ∀ i l : Fin m, ∑ j, P i a * Q b j * (P j c * Q d l) = (if b = c then 1 else 0) * (P i a * Q d l) := by
      intro i l
      rw [← qpApply P Q hQP b c, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    simp only [hc]
    split_ifs <;> simp
  ·
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have e2 : ∀ i j k : Fin m, P i a * Q b j * (P k c * Q d i) = (P k c * Q b j) * (Q d i * P i a) := by
      intros; ring
    simp only [e2]
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]
    simp only [← Finset.sum_smul, ← Finset.mul_sum, qpApply P Q hQP d a]
    split_ifs with h
    · simp only [mul_one]
      exact Finset.sum_comm
    · simp

theorem leibVec {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Y : Fin m → A)
    (P Q : Matrix (Fin m) (Fin m) ℂ) (hQP : Q * P = 1)
    (hL : ∀ a b c, E a b * Y c - Y c * E a b = if a = c then -Y b else 0) (a b c : Fin m) :
    Econj E P Q a b * vecC Q Y c - vecC Q Y c * Econj E P Q a b = if a = c then -vecC Q Y b else 0 := by
  simp only [Econj, vecC]
  simp_rw [commSumA]
  simp_rw [commSumB]
  simp only [smulComm, hL, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  have e : ∀ i j : Fin m, P i a * Q b j * Q c i = Q b j * (Q c i * P i a) := by intros; ring
  simp only [e, ← Finset.sum_smul, ← Finset.mul_sum, qpApply P Q hQP c a]
  split_ifs with h1 h2 h2
  · simp [Finset.sum_neg_distrib]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

theorem leibCov {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Yb : Fin m → A)
    (P Q : Matrix (Fin m) (Fin m) ℂ) (hQP : Q * P = 1)
    (hL : ∀ a b c, E a b * Yb c - Yb c * E a b = if b = c then Yb a else 0) (a b c : Fin m) :
    Econj E P Q a b * covC P Yb c - covC P Yb c * Econj E P Q a b = if b = c then covC P Yb a else 0 := by
  simp only [Econj, covC]
  simp_rw [commSumA]
  simp_rw [commSumB]
  simp only [smulComm, hL, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have e : ∀ i j : Fin m, P i a * Q b j * P j c = P i a * (Q b j * P j c) := by intros; ring
  simp only [e, ← Finset.sum_smul, ← Finset.mul_sum, qpApply P Q hQP b c]
  split_ifs <;> simp

theorem commVec {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (Y : Fin m → A) (Q : Matrix (Fin m) (Fin m) ℂ)
    (hYY : ∀ a b, Y a * Y b = Y b * Y a) (a b : Fin m) :
    vecC Q Y a * vecC Q Y b = vecC Q Y b * vecC Q Y a := by
  simp only [vecC, Finset.sum_mul_sum, smul_mul_smul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [hYY k l, mul_comm (Q a k)]

theorem commCov {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (Yb : Fin m → A) (P : Matrix (Fin m) (Fin m) ℂ)
    (hYY : ∀ a b, Yb a * Yb b = Yb b * Yb a) (a b : Fin m) :
    covC P Yb a * covC P Yb b = covC P Yb b * covC P Yb a := by
  simp only [covC, Finset.sum_mul_sum, smul_mul_smul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [hYY k l, mul_comm (P k a)]

theorem sum_four_comm_version {A : Type*} [AddCommMonoid A] {m : ℕ} (f : Fin m → Fin m → Fin m → Fin m → A) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  calc _ = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l := Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
    _ = _ := Finset.sum_congr rfl (fun k _ => Finset.sum_comm)

theorem starConj {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {m : ℕ}
    (E : Fin m → Fin m → A) (Hm P Q : Matrix (Fin m) (Fin m) ℂ) (ε : Fin m → ℤˣ)
    (hstar : ∀ a b, star (E a b) = ∑ c, ∑ d, (Hm c b * Hm a d) • E c d)
    (hP : ∀ i j, star (P i j) = Q j i) (hQ : ∀ i j, star (Q i j) = P j i)
    (hHP : ∀ k b, ∑ j, Hm k j * P j b = P k b * ((ε b : ℤ) : ℂ))
    (hQH : ∀ a l, ∑ i, Q a i * Hm i l = ((ε a : ℤ) : ℂ) * Q a l) (a b : Fin m) :
    star (Econj E P Q a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * Econj E P Q b a := by
  simp only [Econj, star_sum, star_smul, hstar, Finset.smul_sum, smul_smul, star_mul', hP, hQ]
  rw [sum_four_comm_version]
  simp only [← Finset.sum_smul, intCastMul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  congr 1
  have h1 : ∑ i, ∑ j, Q a i * P j b * (Hm k j * Hm i l) = (∑ i, Q a i * Hm i l) * (∑ j, Hm k j * P j b) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  rw [h1, hQH, hHP]
  push_cast
  ring

end PI.QnHermHaar
end
end

