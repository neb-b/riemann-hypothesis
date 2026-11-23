module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPureTensorsProductMeasureFiniteAdelic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0282
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0274

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TrMultEnd

structure RepB (G : Type) [Group G] where

  X : Type
  [acg : AddCommGroup X]
  [mod : Module ℂ X]

  ρ : Representation ℂ G X

attribute [instance] RepB.acg RepB.mod

theorem RepB.transport {G : Type} [Group G] {B : RepB G} {X : Type} [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ G X} (h : B = ⟨X, ρ⟩)
    (P : ∀ (X : Type) [AddCommGroup X] [Module ℂ X], Representation ℂ G X → Prop) : P B.X B.ρ ↔ P X ρ := by
  subst h; rfl

theorem exists_family {G : Type} [Group G] [TopologicalSpace G]
    {n₁ : ℕ} {W₁ : Fin n₁ → Type} [∀ i, AddCommGroup (W₁ i)] [∀ i, Module ℂ (W₁ i)] (A : ∀ i, Representation ℂ G (W₁ i))
    {n₂ : ℕ} {W₂ : Fin n₂ → Type} [∀ i, AddCommGroup (W₂ i)] [∀ i, Module ℂ (W₂ i)] (B : ∀ i, Representation ℂ G (W₂ i))
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W) :
    ∃ (m : ℕ) (Ws : Fin m → Type) (_ : ∀ i, AddCommGroup (Ws i)) (_ : ∀ i, Module ℂ (Ws i))
      (τ : ∀ i, Representation ℂ G (Ws i)),
      (∀ i j, i ≠ j → IsEmpty ((τ i).Equiv (τ j))) ∧
      (∀ i, ∃ j, Nonempty ((A i).Equiv (τ j))) ∧ (∀ i, ∃ j, Nonempty ((B i).Equiv (τ j))) ∧
      (∀ P : ∀ (X : Type) [AddCommGroup X] [Module ℂ X], Representation ℂ G X → Prop,
        (∀ i, P _ (A i)) → (∀ i, P _ (B i)) → P W σ → ∀ j, P _ (τ j)) ∧
      ∃ j₀, ∀ P : ∀ (X : Type) [AddCommGroup X] [Module ℂ X], Representation ℂ G X → Prop, P W σ → P _ (τ j₀) := by
  let b : Fin (n₁ + n₂ + 1) → RepB G :=
    Fin.append (Fin.append (fun i => (⟨W₁ i, A i⟩ : RepB G)) fun i => ⟨W₂ i, B i⟩) fun _ : Fin 1 => ⟨W, σ⟩
  have hbA : ∀ i, b (Fin.castAdd 1 (Fin.castAdd n₂ i)) = ⟨W₁ i, A i⟩ := fun i => by simp [b]
  have hbB : ∀ i, b (Fin.castAdd 1 (Fin.natAdd n₁ i)) = ⟨W₂ i, B i⟩ := fun i => by simp [b]
  have hbσ : b (Fin.natAdd (n₁ + n₂) 0) = ⟨W, σ⟩ := by simp [b]
  have hb : ∀ k, (∃ i, b k = ⟨W₁ i, A i⟩) ∨ (∃ i, b k = ⟨W₂ i, B i⟩) ∨ b k = ⟨W, σ⟩ := by
    intro k
    refine Fin.addCases (fun k' => ?_) (fun k' => ?_) k
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) k'
      · exact Or.inl ⟨i, hbA i⟩
      · exact Or.inr (Or.inl ⟨i, hbB i⟩)
    · exact Or.inr (Or.inr (by rw [Subsingleton.elim k' 0]; exact hbσ))
  obtain ⟨n, s, hne, ⟨j₀, hj₀⟩, hcov⟩ :=
    _root_.GlobalTheory.TrUnion.exists_reps_through G (n₁ + n₂ + 1) (fun k => (b k).X) (fun k => (b k).ρ) (Fin.natAdd (n₁ + n₂) 0)
  refine ⟨n, fun j => (b (s j)).X, fun j => inferInstance, fun j => inferInstance, fun j => (b (s j)).ρ, hne,
    fun i => ?_, fun i => ?_, fun P hA hB hσ k => ?_, j₀, fun P hP => ?_⟩
  · obtain ⟨j, hj⟩ := hcov (Fin.castAdd 1 (Fin.castAdd n₂ i))
    exact ⟨j, (RepB.transport (hbA i) (fun X _ _ ρ => Nonempty (ρ.Equiv ((b (s j)).ρ)))).1 hj⟩
  · obtain ⟨j, hj⟩ := hcov (Fin.castAdd 1 (Fin.natAdd n₁ i))
    exact ⟨j, (RepB.transport (hbB i) (fun X _ _ ρ => Nonempty (ρ.Equiv ((b (s j)).ρ)))).1 hj⟩
  · rcases hb (s k) with ⟨i, h⟩ | ⟨i, h⟩ | h
    · exact (RepB.transport h P).2 (hA i)
    · exact (RepB.transport h P).2 (hB i)
    · exact (RepB.transport h P).2 hσ
  · exact (RepB.transport ((congrArg b hj₀).trans hbσ) P).2 hP

def equivComp {G H : Type} [Group G] [Group H] {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {ρ' : Representation ℂ G Y} (e : ρ.Equiv ρ') (f : H →* G) :
    Representation.Equiv (ρ.comp f : Representation ℂ H X) (ρ'.comp f) :=
  Representation.Equiv.mk e.toLinearEquiv fun h => by
    ext x; exact congrArg (fun l : X →ₗ[ℂ] Y => l x) (e.isIntertwining' (f h))

def equivCompSymm {G H : Type} [Group G] [Group H] {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (Φ : G ≃* H) :
    Representation.Equiv ρ (((ρ.comp Φ.symm.toMonoidHom : Representation ℂ H X).comp Φ.toMonoidHom : Representation ℂ G X)) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ X) fun g => by ext x; simp

def equivCompSymm' {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ H X) (Φ : G ≃ₜ* H) :
    Representation.Equiv ρ (((ρ.comp Φ.symm.symm.toMulEquiv.toMonoidHom : Representation ℂ G X).comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ H X)) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ X) fun g => by
    ext x
    change ρ g x = ρ (Φ (Φ.symm g)) x
    rw [Φ.apply_symm_apply]

end GlobalTheory.TrMultEnd

namespace GlobalTheory.TrMultEnd


end GlobalTheory.TrMultEnd
