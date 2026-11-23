module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.SmoothLevZero

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.LowerRightNeZeroOfUpperRightZero
section
open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem mulAM {A : Type*} [Ring A] [Algebra ℂ A] (X : A) (c : ℂ) : X * algebraMap ℂ A c = c • X := by
  rw [Algebra.smul_def, Algebra.commutes]

theorem swap4a {A : Type*} [AddCommMonoid A] {p q : ℕ} (F : Fin p → Fin q → Fin p → Fin q → A) :
    ∑ i, ∑ k, ∑ j, ∑ l, F i k j l = ∑ j, ∑ i, ∑ l, ∑ k, F i k j l := by
  calc ∑ i, ∑ k, ∑ j, ∑ l, F i k j l = ∑ i, ∑ j, ∑ k, ∑ l, F i k j l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ l, ∑ k, F i k j l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ l, ∑ k, F i k j l := Finset.sum_comm

theorem swap4b {A : Type*} [AddCommMonoid A] {p q : ℕ} (F : Fin p → Fin q → Fin p → Fin q → A) :
    ∑ i, ∑ k, ∑ j, ∑ l, F i k j l = ∑ i, ∑ j, ∑ k, ∑ l, F i k j l :=
  Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem nested_minor_expansion_one_one {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin (t + 2) → Fin (t + 2) → A)
    (Y Yb : Fin (t + 2) → A) (x xb : Fin (t + 2) → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 1 1 = -∑ i : Fin (t + 2), ∑ k : Fin (t + 1), ∑ j : Fin (t + 2), ∑ l : Fin (t + 1),
      ((-1 : ℂ) ^ ((i : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (l : ℕ)) * xb i * x j) •
        (Yb (i.succAbove k) * Y (j.succAbove l) *
          qminor E (i.succAbove ∘ k.succAbove) (j.succAbove ∘ l.succAbove) (u - 1)) := by
  simp only [tA]
  congr 1

  set G : (Fin t → Fin (t + 2)) → A := fun s => ∑ j : Fin (t + 2), ∑ j' : Fin (t + 2),
    (if j < j' then ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ))) •
      ((Y j * algebraMap ℂ A (x j') - Y j' * algebraMap ℂ A (x j)) * qminor E s (skip2 j j') (u - 1)) else 0)
    with hG
  have h1 : ∀ i i' : Fin (t + 2), (∑ j : Fin (t + 2), ∑ j' : Fin (t + 2),
      if i < i' ∧ j < j' then
        ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ))) •
          ((Yb i * algebraMap ℂ A (xb i') - Yb i' * algebraMap ℂ A (xb i)) *
            (Y j * algebraMap ℂ A (x j') - Y j' * algebraMap ℂ A (x j)) *
            qminor E (skip2 i i') (skip2 j j') (u - 1))
      else 0) =
      if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ))) •
        ((Yb i * algebraMap ℂ A (xb i') - Yb i' * algebraMap ℂ A (xb i)) * G (skip2 i i')) else 0 := by
    intro i i'
    by_cases hi : i < i'
    · simp only [hi, true_and, if_true, hG, Finset.mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))
      split_ifs
      · rw [mul_smul_comm, smul_smul, ← pow_add, mul_assoc]
        congr 2
        ring
      · simp
    · simp [hi]
  simp only [h1]
  have hp := pairSum Yb (fun i => algebraMap ℂ A (xb i)) G
  try simp only at hp
  rw [hp]
  have hq : ∀ s : Fin t → Fin (t + 2), G s = ∑ j : Fin (t + 2), ∑ l : Fin (t + 1),
      ((-1 : ℂ) ^ ((j : ℕ) + (l : ℕ))) • (Y (j.succAbove l) * algebraMap ℂ A (x j) *
        qminor E s (j.succAbove ∘ l.succAbove) (u - 1)) := by
    intro s
    have h := pairSum Y (fun j => algebraMap ℂ A (x j)) (fun s' => qminor E s s' (u - 1))
    rw [hG]
    exact h
  simp only [hq, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ =>
    Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))))
  simp only [mulAM, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  congr 1
  ring

theorem transfer_commutator_one_one (hMV : MoveVec) (hMC : MoveCov) {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ}
    (E : Fin (t + 2) → Fin (t + 2) → A) (Y Yb : Fin (t + 2) → A) (hGl : GlRel E)
    (hYY : ∀ a b, Y a * Y b = Y b * Y a) (hYbYb : ∀ a b, Yb a * Yb b = Yb b * Yb a)
    (hLY : ∀ a b c, E a b * Y c - Y c * E a b = if a = c then -Y b else 0)
    (hLYb : ∀ a b c, E a b * Yb c - Yb c * E a b = if b = c then Yb a else 0)
    (a b : Fin (t + 2)) (w : ℂ) :
    ∑ k : Fin (t + 1), ∑ l : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
        (qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) w * Yb (a.succAbove k) *
          Y (b.succAbove l)) =
      ∑ k : Fin (t + 1), ∑ l : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
        (Yb (a.succAbove k) * Y (b.succAbove l) *
          qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) w) := by
  have hz : ∀ (p : ℕ) (X : A), (((-1 : ℤ) ^ p : ℤ) : A) * X = ((-1 : ℂ) ^ p) • X := by
    intro p X
    rw [← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul ℂ]
    push_cast
    try rfl
  have MC := fun l : Fin (t + 1) =>
    hMC A (t + 2) t E Yb hGl hLYb hYbYb a.succAbove (b.succAbove ∘ l.succAbove) w
  have MV := fun k : Fin (t + 1) =>
    hMV A (t + 2) t E Y hGl hLY hYY (a.succAbove ∘ k.succAbove) b.succAbove w
  simp only [hz] at MC MV
  have h1 : ∀ l : Fin (t + 1), ∑ k : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
      (qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) w *
        (Yb (a.succAbove k) * Y (b.succAbove l))) =
      ∑ k : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
      (Yb (a.succAbove k) *
        (qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) (w - 1) * Y (b.succAbove l))) := by
    intro l
    have e := congrArg (fun S => ((-1 : ℂ) ^ (l : ℕ)) • (S * Y (b.succAbove l))) (MC l)
    simp only [Finset.sum_mul, Finset.smul_sum, smul_mul_assoc, smul_smul, mul_assoc,
      mul_comm ((-1 : ℂ) ^ (l : ℕ))] at e
    exact e.symm
  have h2 : ∀ k : Fin (t + 1), ∑ l : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
      (Yb (a.succAbove k) *
        (qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) (w - 1) * Y (b.succAbove l))) =
      ∑ l : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
      (Yb (a.succAbove k) * (Y (b.succAbove l) *
        qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) w)) := by
    intro k
    have e := congrArg (fun S => ((-1 : ℂ) ^ (k : ℕ)) • (Yb (a.succAbove k) * S)) (MV k)
    simp only [Finset.mul_sum, Finset.smul_sum, mul_smul_comm, smul_smul] at e
    exact e.symm
  simp only [mul_assoc]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun l _ => h1 l, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => h2 k

theorem starY {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {m : ℕ} (Y Yb : Fin m → A)
    (ε : Fin m → ℤˣ) (hYb : ∀ c, Yb c = ((ε c : ℤ) : ℂ) • star (Y c)) (c : Fin m) :
    star (Y c) = ((ε c : ℤ) : ℂ) • Yb c := by
  have he : ((ε c : ℤ) : ℂ) * ((ε c : ℤ) : ℂ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [hYb c, smul_smul, he, one_smul]

theorem starYb {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {m : ℕ} (Y Yb : Fin m → A)
    (ε : Fin m → ℤˣ) (hYb : ∀ c, Yb c = ((ε c : ℤ) : ℂ) • star (Y c)) (c : Fin m) :
    star (Yb c) = ((ε c : ℤ) : ℂ) • Y c := by
  rw [hYb c, star_smul, star_star, star_intCast]

theorem lower_right_ne_zero_of_upper_right_zero (hSM : StarMinor) (hMV : MoveVec) (hMC : MoveCov) {A : Type} [Ring A] [StarRing A]
    [Algebra ℂ A] [StarModule ℂ A] {m : ℕ}
    (E : Fin m → Fin m → A) (Y Yb : Fin m → A) (x xb : Fin m → ℂ) (ε : Fin m → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a)
    (hYY : ∀ a b, Y a * Y b = Y b * Y a) (hYbYb : ∀ a b, Yb a * Yb b = Yb b * Yb a)
    (hLY : ∀ a b c, E a b * Y c - Y c * E a b = if a = c then -Y b else 0)
    (hLYb : ∀ a b c, E a b * Yb c - Yb c * E a b = if b = c then Yb a else 0)
    (hYb : ∀ c, Yb c = ((ε c : ℤ) : ℂ) • star (Y c)) (hxb : ∀ c, xb c = ((ε c : ℤ) : ℂ) * star (x c))
    (u : ℂ) :
    star (tA E Y Yb x xb u 1 1) = tA E Y Yb x xb (star u) 1 1 := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m <;> simp [tA]
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 2 := ⟨m - 2, by omega⟩
  have hterm : ∀ (i : Fin (t + 2)) (k : Fin (t + 1)) (j : Fin (t + 2)) (l : Fin (t + 1)),
      star (((-1 : ℂ) ^ ((i : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (l : ℕ)) * xb i * x j) •
        (Yb (i.succAbove k) * Y (j.succAbove l) *
          qminor E (i.succAbove ∘ k.succAbove) (j.succAbove ∘ l.succAbove) (u - 1))) =
      ((-1 : ℂ) ^ ((i : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (l : ℕ)) * xb j * x i) •
        (qminor E (j.succAbove ∘ l.succAbove) (i.succAbove ∘ k.succAbove) (star u - 1) *
          Yb (j.succAbove l) * Y (i.succAbove k)) := by
    intro i k j l
    rw [star_smul, star_mul (Yb _ * Y _), star_mul (Yb _), star2 hSM E ε hGl hE, starY Y Yb ε hYb, starYb Y Yb ε hYb,
      star_sub, star_one]
    simp only [star_mul', star_pow, star_neg, star_one, hxb, starE, star_star]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    congr 1
    have h1 := eSq (ε i)
    have h2 := eSq (ε (i.succAbove k))
    have h4 := eSq (ε (j.succAbove l))
    set p2 := ((ε (i.succAbove k) : ℤ) : ℂ)
    set p4 := ((ε (j.succAbove l) : ℤ) : ℂ)
    linear_combination ((-1 : ℂ) ^ ((i : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (l : ℕ)) * x i * star (x j) *
      ((ε j : ℤ) : ℂ)) * (p2 * p2 * p4 * p4 * h1 + p4 * p4 * h2 + h4)
  rw [nested_minor_expansion_one_one, nested_minor_expansion_one_one]
  simp only [star_neg, star_sum, hterm]
  congr 1
  conv_lhs => rw [swap4a]
  conv_rhs => rw [swap4b]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  have eL : ∑ l : Fin (t + 1), ∑ k : Fin (t + 1),
      ((-1 : ℂ) ^ ((b : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((a : ℕ) + (l : ℕ)) * xb a * x b) •
        (qminor E (a.succAbove ∘ l.succAbove) (b.succAbove ∘ k.succAbove) (star u - 1) *
          Yb (a.succAbove l) * Y (b.succAbove k)) =
      ((-1 : ℂ) ^ (a : ℕ) * (-1 : ℂ) ^ (b : ℕ) * xb a * x b) • ∑ l : Fin (t + 1), ∑ k : Fin (t + 1),
        ((-1 : ℂ) ^ (l : ℕ) * (-1 : ℂ) ^ (k : ℕ)) •
          (qminor E (a.succAbove ∘ l.succAbove) (b.succAbove ∘ k.succAbove) (star u - 1) *
            Yb (a.succAbove l) * Y (b.succAbove k)) := by
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
    congr 1
    ring
  have eR : ∑ k : Fin (t + 1), ∑ l : Fin (t + 1),
      ((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((b : ℕ) + (l : ℕ)) * xb a * x b) •
        (Yb (a.succAbove k) * Y (b.succAbove l) *
          qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) (star u - 1)) =
      ((-1 : ℂ) ^ (a : ℕ) * (-1 : ℂ) ^ (b : ℕ) * xb a * x b) • ∑ k : Fin (t + 1), ∑ l : Fin (t + 1),
        ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
          (Yb (a.succAbove k) * Y (b.succAbove l) *
            qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) (star u - 1)) := by
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    congr 1
    ring
  rw [eL, eR, transfer_commutator_one_one hMV hMC E Y Yb hGl hYY hYbYb hLY hLYb a b (star u - 1)]

end PI.QnHermHaar
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.RepOnOfEq
section
open Matrix Finset MeasureTheory
open scoped ContDiff

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}

theorem repOn_of_eq {hI' : IntOn μ (ιo k r) (testSub k r i)} {T : A hI'} {Φ Ψ : (Mx k r → ℂ) → Mx k r → ℂ}
    (h : RepOn hI' T Φ) (e : ∀ f, Φ f = Ψ f) : RepOn hI' T Ψ := by
  have hΦΨ : Φ = Ψ := funext e
  subst hΦΨ
  exact h

private theorem eq_of_repOn_of_agree_on_test (H : Hyp k r z z' i μ) {S T : A (hI H)}
    {Φ Ψ : (Mx k r → ℂ) → Mx k r → ℂ} (hS : RepOn (hI H) S Φ) (hT : RepOn (hI H) T Ψ)
    (e : ∀ f, TestF k r i f → ∀ g ∈ Glev k r i, Φ f g = Ψ f g) : S = T :=
  A_ext (hI H) fun f hf => by
    rw [(hS f hf).2, (hT f hf).2]
    exact mk'_eq_of_eqOn (hI H) (Glev k r i) (hG H) (hS f hf).1 (hT f hf).1 (e f hf)

private theorem repOn_ite' (H : Hyp k r z z' i μ) (p : Prop) [Decidable p] {T : A (hI H)}
    {Φ : (Mx k r → ℂ) → Mx k r → ℂ} (hT : RepOn (hI H) T Φ) :
    RepOn (hI H) (if p then T else 0) (fun f g => if p then Φ f g else 0) := by
  by_cases hp : p
  · simp only [if_pos hp]
    exact hT
  · simp only [if_neg hp]
    have h0 := repOn_sub _ hT hT
    rw [sub_self] at h0
    exact repOn_of_eq h0 fun f => funext fun g => by simp

theorem glRel_A (H : Hyp k r z z' i μ) : GlRel (EA H) := by
  intro a b c d
  refine eq_of_repOn_of_agree_on_test H (repOn_sub _ (repOn_mul _ (repE H a b) (repE H c d)) (repOn_mul _ (repE H c d) (repE H a b)))
    (repOn_sub _ (repOn_ite' H (b = c) (repE H a d)) (repOn_ite' H (d = a) (repE H c b))) fun f hf g hg => ?_
  exact H.Gl ℂ k r i Set.univ a b c d f isOpen_univ hf.1 g ⟨hg, Set.mem_univ _⟩

theorem starE_A (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) :
    star (EA H a b) = ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EA H c d := by
  have hL : RepOn (hI H) (star (EA H a b)) (EOp' k r i a b) := by
    show RepOn (hI H) (star (toA (hI H) (hG H) (adjOp_E H a b))) _
    rw [star_toA]
    exact repOn_toA _ _ _
  have hR : RepOn (hI H) (∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EA H c d)
      (fun f => ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EOp k r i c d f) :=
    repOn_sum _ _ fun c _ => repOn_sum _ _ fun d _ => repOn_smul _ _ (repE H c d)
  refine eq_of_repOn_of_agree_on_test H hL hR fun f _ g _ => ?_
  simp only [EOp'_eq]

theorem yComm (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) : YA H a * YA H b = YA H b * YA H a := by
  refine eq_of_repOn_of_agree_on_test H (repOn_mul _ (repY H a) (repY H b)) (repOn_mul _ (repY H b) (repY H a)) fun f _ g _ => ?_
  simp only [MOp]
  ring

theorem ybComm (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) : YbA H a * YbA H b = YbA H b * YbA H a := by
  refine eq_of_repOn_of_agree_on_test H (repOn_mul _ (repYb H a) (repYb H b)) (repOn_mul _ (repYb H b) (repYb H a)) fun f _ g _ => ?_
  simp only [MOp]
  ring

theorem yybComm (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) : YA H a * YbA H b = YbA H b * YA H a := by
  refine eq_of_repOn_of_agree_on_test H (repOn_mul _ (repY H a) (repYb H b)) (repOn_mul _ (repYb H b) (repY H a)) fun f _ g _ => ?_
  simp only [MOp]
  ring

theorem eyComm (H : Hyp k r z z' i μ) (a b c : Fin (mdim k r i)) :
    EA H a b * YA H c - YA H c * EA H a b = if a = c then -YA H b else 0 := by
  refine eq_of_repOn_of_agree_on_test H (repOn_sub _ (repOn_mul _ (repE H a b) (repY H c)) (repOn_mul _ (repY H c) (repE H a b)))
    (repOn_ite' H (a = c) (repOn_neg _ (repY H b))) fun f hf g hg => ?_
  have hy := (H.YL ℂ k r z i Set.univ a b c f isOpen_univ hf.1 g ⟨hg, Set.mem_univ _⟩).1
  show EH k r (posL k r i a) (posL k r i b) (fun x => yv k r z i x c • f x) g -
      yv k r z i g c * EH k r (posL k r i a) (posL k r i b) f g =
      if a = c then -(yv k r z i g b * f g) else 0
  rw [hy]
  split_ifs <;> simp only [smul_eq_mul] <;> ring

theorem eybComm (H : Hyp k r z z' i μ) (a b c : Fin (mdim k r i)) :
    EA H a b * YbA H c - YbA H c * EA H a b = if b = c then YbA H a else 0 := by
  refine eq_of_repOn_of_agree_on_test H (repOn_sub _ (repOn_mul _ (repE H a b) (repYb H c)) (repOn_mul _ (repYb H c) (repE H a b)))
    (repOn_ite' H (b = c) (repYb H a)) fun f hf g hg => ?_
  have hy := (H.YL ℂ k r z i Set.univ a b c f isOpen_univ hf.1 g ⟨hg, Set.mem_univ _⟩).2
  show EH k r (posL k r i a) (posL k r i b) (fun x => ybv k r z i x c • f x) g -
      ybv k r z i g c * EH k r (posL k r i a) (posL k r i b) f g =
      if b = c then ybv k r z i g a * f g else 0
  rw [hy]
  split_ifs <;> simp only [smul_eq_mul] <;> ring

theorem ybStar (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) :
    YbA H c = ∑ l, Hm k r i l c • star (YA H l) := by
  have hs : ∀ l, RepOn (hI H) (star (YA H l)) (MOp' (fun g => yv k r z i g l)) := fun l => by
    show RepOn (hI H) (star (toA (hI H) (hG H) (adjOp_M _ (yTest H l)))) _
    rw [star_toA]
    exact repOn_toA _ _ _
  refine eq_of_repOn_of_agree_on_test H (repYb H c) (repOn_sum _ _ fun l _ => repOn_smul _ _ (hs l)) fun f _ g hg => ?_
  simp only [MOp, MOp', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [H.Yb k r z i H.hz g hg c, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

end PI.QnHermHaar
end
end

