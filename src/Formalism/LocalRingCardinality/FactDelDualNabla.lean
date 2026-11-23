module

public import Formalism.LocalRingCardinality.DataForced
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0003
public import Formalism.LocalToGlobal.Columns.Bundle0011
public import Formalism.LocalRingCardinality.Bundle0006
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions

open Formalism.MainNotions.G
open scoped BigOperators

theorem posPl_bijective (D : D7) (p e : ℕ) : Function.Bijective (fun z => posPl D p z e) := by
  have hinj : Function.Injective (fun z => posPl D p z e) := by
    intro z z' h
    have h' := congrArg (fun y => posPl D p y (nP D p * e - e)) h
    simp only [posPl_add] at h'
    have he : e + (nP D p * e - e) = nP D p * e := by
      have : e ≤ nP D p * e := Nat.le_mul_of_pos_left e (Nat.pos_of_ne_zero (NeZero.ne _))
      omega
    rwa [he, posPl_mul_period, posPl_mul_period] at h'
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

theorem tauPl_bij (D : D7) : Function.Bijective (tauPl D) := by
  have hI := D.R.toFrame.iota_bijective.1
  have hP := factPlaces D.R.toFrame
  constructor
  · rintro ⟨β, t⟩ ⟨β', t'⟩ h
    have h1 : plGG D (β, t) = plGG D (β', t') := congrArg Subtype.val (D.eTau.symm.injective h)
    cases β <;> cases β'
    · have h2 : D.R.tau1 t = D.R.tau1 t' := h1
      rw [hI (Prod.ext_iff.1 h2).2]
    · exact absurd (show D.R.tau1 t = D.R.tau2 t' from h1) (hP.2 t t')
    · exact absurd (show D.R.tau1 t' = D.R.tau2 t from h1.symm) (hP.2 t' t)
    · have h2 : D.R.tau2 t = D.R.tau2 t' := h1
      rw [hI (Prod.ext_iff.1 h2).2]
  · intro τ
    rcases (hP.1 _).1 (D.eTau τ).2 with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨(false, t), (Equiv.symm_apply_eq _).2 (Subtype.ext ht.symm)⟩
    · exact ⟨(true, t), (Equiv.symm_apply_eq _).2 (Subtype.ext ht.symm)⟩

theorem lpF_ge_sum (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) (hl : 2 ≤ l) (hD : ∀ s, 0 ≤ Ds s) :
    (∑ s, Ds s) / ((l : ℝ) ^ 2 - 1) ≤ lpF l d Ds :=
  lp_lower_bound l d Ds hl hD

theorem fInertGe (D : D7) : FInertGe D := by
  intro j _ p hp _ hw
  have hk : 0 ≤ (D.R.k : ℝ) - 1 := by
    have h := D.R.m_add_three_le_k
    have h1 : (1 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    linarith
  have hwP : ∀ z, 0 ≤ wPl D j z := fun z => hw _
  unfold FInert
  split_ifs with h
  · exact le_rfl
  · have hn : (0 : ℝ) < (nP D p : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne _))
    rw [le_div_iff₀ hn]
    have h1 : ∀ z, (∑ s : ZMod (nP D p), ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s.val)) / ((p : ℝ) ^ 2 - 1) ≤
        FOrb D j p z :=
      fun z => lpF_ge_sum p (nP D p) _ hp.two_le (fun s => mul_nonneg hk (hwP _))
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun z _ => h1 z)
    have h2 : ∀ s : ZMod (nP D p), ∑ z : Bool × HH D, ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s.val) =
        ∑ τ : D.what₂.Tau, ((D.R.k : ℝ) - 1) * wj D j τ := fun s => by
      rw [(posPl_bijective D p s.val).sum_comp (fun z => ((D.R.k : ℝ) - 1) * wPl D j z)]
      exact (tauPl_bij D).sum_comp (fun τ => ((D.R.k : ℝ) - 1) * wj D j τ)
    have h3 : ∑ z : Bool × HH D, ∑ s : ZMod (nP D p), ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s.val) =
        (nP D p : ℝ) * ∑ τ : D.what₂.Tau, ((D.R.k : ℝ) - 1) * wj D j τ := by
      rw [Finset.sum_comm, Finset.sum_congr rfl fun s _ => h2 s, Finset.sum_const, Finset.card_univ, ZMod.card,
        nsmul_eq_mul]
    rw [← Finset.sum_div, ← Finset.sum_div, h3]
    ring

theorem factDelDualNabla : FactDelDualNabla := factDelDualNabla_of Formalism.L2.DIV.weylEqDualNabla

section Check

end Check

end Formalism.BasicNotions

end
