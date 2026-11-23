module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.BZSeg

section Props

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def GenericProdIff : Prop :=
  ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (π a)) →
    (IsGeneric (multiProd (stdBlocks d hd) π) ↔ ∀ a, IsGeneric (π a))

def WhitRankIrr : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    Module.rank ℂ (TwJacquet π (unipB k (Fin N)) (whitChar ψ N)) ≤ 1

def CuspGeneric : Prop :=
  ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 0 < N → IsSmooth π →
    π.IsIrreducible → IsCuspidal π → IsGeneric π

def LSegGeneric : Prop :=
  ∀ (Δ : Segment k) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsLSeg Δ π → IsGeneric π

def ProdIrrFiniteLength : Prop :=
  ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), HasFiniteLength (prodIrr x hd)

def LUnlinkedIrr : Prop :=
  ∀ (h N : ℕ) (Δ : Fin h → Segment k) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N),
    (∀ i j, ¬ (Δ i).Linked (Δ j)) → (∀ i, IsLSeg (Δ i) (x i).rep) → (prodIrr x hd).IsIrreducible

def LUnlinkedComm : Prop :=
  ∀ (Δ Δ' : Segment k) (x y : IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N) (hd' : ∑ a, (![y, x] a).1 = N),
    ¬ Δ.Linked Δ' → IsLSeg Δ x.rep → IsLSeg Δ' y.rep → Nonempty ((prodIrr ![x, y] hd).Equiv (prodIrr ![y, x] hd'))

end Props

end GlobalTheory.BZSeg

end
