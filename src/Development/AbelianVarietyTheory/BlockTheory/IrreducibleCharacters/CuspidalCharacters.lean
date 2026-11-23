module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002

@[expose] public section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters

open Matrix

theorem isIrreducible_iff {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    ρ.IsIrreducible ↔ Nontrivial V ∧
      ∀ U : Submodule ℂ V, (∀ g : G, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  first
  | exact @_root_.GlobalTheory.UnimodularLatticeExistence.main
  | exact _root_.GlobalTheory.UnimodularLatticeExistence.main
  | (apply _root_.GlobalTheory.UnimodularLatticeExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnimodularLatticeExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnimodularLatticeExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnimodularLatticeExistence.main ..)

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters
