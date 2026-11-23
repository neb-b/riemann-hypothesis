module

public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementW
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.AntitoneOfMemGtBox

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

namespace WGT

open Formalism.InvariantFactorPaths.GelfandTsetlinBases (gtBox dGT stripsUp)

lemma extW_lt {n : ℕ} (la : Fin n → ℤ) {m : ℕ} (h : m < n) : extW la m = la ⟨m, h⟩ := by
  simp [extW, h]

lemma extW_val {n : ℕ} (la : Fin n → ℤ) (i : Fin n) : extW la i.val = la i := by
  simp [extW]

lemma dom_iff {n : ℕ} (μ : Fin n → ℤ) : Dom n (extW μ) ↔ Antitone μ := by
  constructor
  · intro h a b hab
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    simp only [Fin.mk_le_mk] at hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ k hak ih =>
      have h1 := h k hb
      rw [extW_lt μ hb, extW_lt μ (by omega)] at h1
      exact le_trans h1 (ih (by omega))
  · intro h m hm
    rw [extW_lt μ hm, extW_lt μ (by omega)]
    exact h (Fin.mk_le_mk.mpr (Nat.le_succ m))

lemma interl_iff {n : ℕ} (la : Fin n → ℤ) (μ : Fin (n + 1) → ℤ) :
    Interl n (extW la) (extW μ) ↔ la ∈ gtBox μ := by
  simp only [gtBox, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · intro h i
    have h1 := h i.val i.isLt
    rw [extW_val, extW_lt μ (by omega), extW_lt μ (by omega)] at h1
    exact ⟨h1.2, h1.1⟩
  · intro h l hl
    have h1 := h ⟨l, hl⟩
    rw [extW_lt la hl, extW_lt μ (by omega), extW_lt μ (by omega)]
    exact ⟨h1.2, h1.1⟩

lemma finsum_prop_eq_sum {α : Type*} (p : α → Prop) (s : Finset α) (f : α → ℝ) (h : ∀ a, p a ↔ a ∈ s) :
    ∑ᶠ (a : α) (_ : p a), f a = ∑ a ∈ s, f a := by
  simp_rw [h]
  exact finsum_mem_finset_eq_sum f s

end WGT

open WGT in
theorem weyl_dim_eq_gelfand_tsetlin : WeylGT := by
  intro hB n
  induction n with
  | zero =>
    intro μ _
    simp [weylDim, Formalism.InvariantFactorPaths.GelfandTsetlinBases.dGT]
  | succ n ih =>
    intro μ hμ
    rw [← hB n μ ((dom_iff μ).mpr hμ), finsum_prop_eq_sum _ (Formalism.InvariantFactorPaths.GelfandTsetlinBases.gtBox μ) _ (fun la => interl_iff la μ),
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.dGT_succ, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun la hla => ih la ?_)
    have hI := (interl_iff la μ).mpr hla
    apply (dom_iff la).mp
    intro m hm
    exact le_trans (hI (m + 1) hm).1 (hI m (by omega)).2


end Formalism.InvariantFactorPaths.BranchingDimensions
