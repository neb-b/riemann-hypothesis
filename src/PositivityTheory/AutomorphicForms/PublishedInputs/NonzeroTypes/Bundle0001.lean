module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.GIface
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def HasDetVec {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V)
    (η : kˣ →* ℂˣ) : Prop :=
  ∃ v : V, v ≠ 0 ∧ ∀ g ∈ KO k (Fin N), ρ g v = (η (GeneralLinearGroup.det g) : ℂ) • v

def IsTwSphProd {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    {s : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = n) (η : Fin s → kˣ →* ℂˣ) : Prop :=
  ∃ (X : Fin s → Type) (_ : ∀ a, AddCommGroup (X a)) (_ : ∀ a, Module ℂ (X a))
    (σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    (∀ a, IsSmooth (σ a)) ∧ (∀ a, (σ a).IsIrreducible) ∧ (∀ a, HasDetVec (σ a) (η a)) ∧
      Nonempty (π.Equiv (multiProd (stdBlocks d hd) σ))

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.InPow
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def InPow (c : ℕ) (x : k) : Prop :=
  ∃ y : 𝒪[k], y ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c ∧ algebraMap 𝒪[k] k y = x

def cond (ψ : 𝒪[k]ˣ →* ℂˣ) : ℕ :=
  sInf {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → ψ u = 1}

abbrev res (μ : kˣ →* ℂˣ) : 𝒪[k]ˣ →* ℂˣ := μ.comp (unitIncl k)

def cc {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b : Fin s) : ℕ := cond (res (μ a / μ b))


variable (k) in
structure Grp (n : ℕ) where
  s : ℕ
  d : Fin s → ℕ
  pos : ∀ a, 0 < d a
  hd : ∑ a, d a = n
  μ : Fin s → kˣ →* ℂˣ
  smooth : ∀ a, IsSmoothChar (μ a)
  dist : ∀ a b, a ≠ b → res (μ a) ≠ res (μ b)
  ball : ∀ a a' b' b : Fin s, a ≤ a' → a' < b' → b' ≤ b → cc μ a' b' ≤ cc μ a b

namespace Grp

variable {n : ℕ} (G : Grp k n)

abbrev e : (Σ a, Fin (G.d a)) ≃ Fin n := stdBlocks G.d G.hd

abbrev bl (i : Fin n) : Fin G.s := (G.e.symm i).1

abbrev chi (i : Fin n) : kˣ →* ℂˣ := G.μ (G.bl i)

end Grp

end UpperTheory.TNZ
end
end

