module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.Interface

@[expose] public section

noncomputable section
open scoped BigOperators
open Classical

namespace GlobalTheory.RowValueCheck

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

def Agree {σ : Type} (S : Set σ) (F F' : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, (∀ x, μ x ≠ 0 → x ∈ S) → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ F'

theorem Agree.mul {σ : Type} {S : Set σ} {F F' K K' : MvPowerSeries σ C} (h : Agree S F F')
    (h' : Agree S K K') : Agree S (F * K) (F' * K') := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have e : p.1 + p.2 = μ := by simpa using hp
  rw [h p.1 fun x hx => hμ x (by rw [← e]; simp; omega),
    h' p.2 fun x hx => hμ x (by rw [← e]; simp; omega)]

theorem Agree.pow {σ : Type} {S : Set σ} {F F' : MvPowerSeries σ C} (h : Agree S F F') (k : ℕ) :
    Agree S (F ^ k) (F' ^ k) := by
  induction k with
  | zero => intro μ _; simp
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem Agree.exp {σ : Type} {S : Set σ} {F F' : MvPowerSeries σ C} (h : Agree S F F') :
    Agree S (mvExp F) (mvExp F') := by
  intro μ hμ
  show (∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (F ^ k) / (k.factorial : C)) =
    ∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (F' ^ k) / (k.factorial : C)
  exact Finset.sum_congr rfl fun k _ => by rw [h.pow k μ hμ]

theorem Agree.prod {σ α : Type} {S : Set σ} (s : Finset α) {F F' : α → MvPowerSeries σ C}
    (h : ∀ i, Agree S (F i) (F' i)) : Agree S (∏ i ∈ s, F i) (∏ i ∈ s, F' i) := by
  induction s using Finset.induction_on with
  | empty => intro μ _; simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha]; exact (h a).mul ih

theorem agree_rowCopy {N : ℕ} (S : Set (Fin N × WV I)) (ρ : Fin N) (F F' : MvPowerSeries (WV I) C)
    (h : Agree {w | (ρ, w) ∈ S} F F') : Agree S (rowCopy ρ F) (rowCopy ρ F') := by
  intro μ hμ
  have hs : MvPowerSeries.HasSubst
      (fun w : WV I => (MvPowerSeries.X (ρ, w) : MvPowerSeries (Fin N × WV I) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by simp)
  unfold rowCopy
  rw [MvPowerSeries.coeff_subst hs, MvPowerSeries.coeff_subst hs]
  refine finsum_congr fun e => ?_
  by_cases he : ∀ x, e x ≠ 0 → (ρ, x) ∈ S
  · rw [h e he]
  · push Not at he
    obtain ⟨x, hx, hxS⟩ := he
    have h0 : μ (ρ, x) = 0 := by
      by_contra h1
      exact hxS (hμ _ h1)
    have hd : (MvPowerSeries.X (ρ, x) : MvPowerSeries (Fin N × WV I) C) ∣
        e.prod fun s k => (MvPowerSeries.X (ρ, s) : MvPowerSeries (Fin N × WV I) C) ^ k :=
      (dvd_pow_self _ hx).trans (Finset.dvd_prod_of_mem
        (fun s => (MvPowerSeries.X (ρ, s) : MvPowerSeries (Fin N × WV I) C) ^ e s)
        (Finsupp.mem_support_iff.2 hx))
    rw [MvPowerSeries.X_dvd_iff.1 hd μ h0]
    simp

def hOf (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) :
    Option (Fin 2 × ZMod d × ZMod d) → MvPowerSeries (WV I) C
  | some (g, a, a') => hL g a a'
  | none => 0

theorem valOf_eq (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) {N : ℕ}
    (P : MvPolynomial (Fin N × WV I) C) (kind : Fin N → Option (Fin 2 × ZMod d × ZMod d))
    (gr : Fin N → MvPowerSeries (WV I) C) :
    ValOf hL P kind gr =
      jetAt0 P (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ (hOf hL (kind ρ))))) := by
  unfold ValOf
  congr 1

end GlobalTheory.RowValueCheck
