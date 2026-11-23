module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.HasTypeVecIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0001

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.Gal.TypesAndIwahori

structure Loc : Prop where
  bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  geo : GlobalTheory.Published.GeometricLemma
  zel : GlobalTheory.Published.ZelevinskyPolynomialRing
  disj : GlobalTheory.Published.TotallyDisjointProductIrreducible
  mp : GlobalTheory.Published.MoyPrasadJacquetIso
  dzi : GlobalTheory.Published.DepthZeroInduction
  dzj : GlobalTheory.Published.DepthZeroJacquetInjective

structure LocN : Prop where
  loc : Loc

def Lifts : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    (∀ (η : kˣ →* ℂˣ) (θ : 𝓀[k]ˣ →* ℂˣ), IsTameLift η θ → IsSmoothChar η) ∧
    (∀ θ : 𝓀[k]ˣ →* ℂˣ, ∃ η : kˣ →* ℂˣ, IsTameLift η θ) ∧
    ∀ (η : kˣ →* ℂˣ) (θ θ' : 𝓀[k]ˣ →* ℂˣ), IsTameLift η θ → IsTameLift η θ' → θ = θ'

def FinTri : Prop :=
  ∀ (R : Type) [CommRing R] (N s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = N) (h : GL (Fin N) R),
    (∀ i j, j < i → (h : Matrix (Fin N) (Fin N) R) i j = 0) →
    ∃ hp : h ∈ parab R (stdBlocks d hd), ∀ a,
      ((GeneralLinearGroup.det (leviProj R (stdBlocks d hd) ⟨h, hp⟩ a) : Rˣ) : R) =
        ∏ j : Fin (d a), (h : Matrix (Fin N) (Fin N) R) (stdBlocks d hd ⟨a, j⟩) (stdBlocks d hd ⟨a, j⟩)

def TypeToIw : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (θ : Fin s → 𝓀[k]ˣ →* ℂˣ) (μ : Fin s → kˣ →* ℂˣ),
    (∀ a, IsTameLift (μ a) (θ a)) → ∀ v ∈ typeSp π (stdBlocks d hd) θ,
      GlobalTheory.TameIwahori.IsIwVec (fun i => μ (blockOf d hd i)) π v

def ParaFactor : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n),
    (∀ g : parahoric k e, ∃ (p : parab k e) (x : leviK k m), (p : GL n k) ∈ KO k n ∧ leviProj k e p = (x : Levi k m) ∧
      redLevi k m x = parahoricProj k e g ∧ ∃ c ∈ KOne k n, (g : GL n k) = p * c) ∧
    ∀ p : parab k e, (p : GL n k) ∈ KOne k n → leviProj k e p ∈ leviKOne k m

def IndSupp : Prop :=
  ∀ (G W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (P C : Subgroup G) (σ : Representation ℂ P W) (u : W), IsOpen (C : Set G) → (∀ p : P, (p : G) ∈ C → σ p u = u) →
    ∃ f : smoothPart (ind P σ), (∀ (p : P), ∀ c ∈ C, f.1.1 ((p : G) * c) = σ p u) ∧
      ∀ g : G, (¬ ∃ p : P, ∃ c ∈ C, g = (p : G) * c) → f.1.1 g = 0

def JacOfType : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    ∀ (θ : Fin s → 𝓀[k]ˣ →* ℂˣ) (μ : Fin s → kˣ →* ℂˣ), (∀ a, IsTameLift (μ a) (θ a)) → HasTypeVec π e θ →
    ∃ y : Jacquet π (unipRad k e), y ≠ 0 ∧ ∀ x ∈ leviK k (m := fun a : Fin s => Fin (d a)),
      jacU e π x y = (∏ a, ((μ a (GeneralLinearGroup.det (x a)) : ℂˣ) : ℂ)) • y

def GrpFacts : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (θ : Fin s → 𝓀[k]ˣ →* ℂˣ) (μ : Fin s → kˣ →* ℂˣ), Function.Injective θ → (∀ a, IsTameLift (μ a) (θ a)) →
    ∀ a b, a ≠ b → UpperTheory.TNZ.res (μ a) ≠ UpperTheory.TNZ.res (μ b) ∧ UpperTheory.TNZ.cc μ a b = 1

def JacProd : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (G : UpperTheory.TNZ.Grp k N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    (∃ y : Jacquet π (unipRad k G.e), y ≠ 0 ∧ ∀ x ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)),
      jacU G.e π x y = (∏ a, ((G.μ a (GeneralLinearGroup.det (x a)) : ℂˣ) : ℂ)) • y) →
    UpperTheory.TNZ.IsTwSphProd π G.d G.hd G.μ

def BlockCount : Prop :=
  ∀ (β : Type) (N s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = N) (θ : Fin s → β),
    Finset.univ.val.map (fun i => θ (blockOf d hd i)) = ∑ a, Multiset.replicate (d a) (θ a)

end UpperTheory.Gal.TypesAndIwahori
