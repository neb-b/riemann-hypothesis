module

public import Mathlib
public import Formalism.SatakeDualWeyl.Statement

@[expose] public section

noncomputable section

open TensorProduct

namespace Formalism.RankGapBounds.FormsTensorLocalization

open Formalism.UG

def LatIncl {k : Type} [CommRing k] {A : Type} [AddCommGroup A] [Module k A]
    (l : k) (B : Submodule k A) (e : ℕ) : Prop :=
  ∀ x : A, l ^ e • x ∈ B

def tensSub {k : Type} [CommRing k] {ι : Type} {A : ι → Type} [∀ i, AddCommGroup (A i)]
    [∀ i, Module k (A i)] (B : ∀ i, Submodule k (A i)) : Submodule k (⨂[k] i, A i) :=
  LinearMap.range (PiTensorProduct.map fun i => (B i).subtype)

def formsIn {G : Type} [Group G] {k : Type} [CommRing k] {W : Type} [AddCommGroup W]
    [Module k W] (Γ K : Subgroup G) (ρK : Representation k K W) (U : Submodule k W) :
    Submodule k (G → W) :=
  AMFK k Γ K ρK ⊓ Submodule.pi Set.univ (fun _ => U)

def locSet {T : Type} [CommRing T] {M : Type} [AddCommGroup M] [Module T M]
    (S : Submonoid T) (N : Set M) : Set (LocalizedModule S M) :=
  {y | ∃ x ∈ N, ∃ s : S, LocalizedModule.mk x s = y}

def TensorStep : Prop :=
  ∀ (k : Type) [CommRing k] (ι : Type) [Fintype ι] (A : ι → Type) [∀ i, AddCommGroup (A i)]
    [∀ i, Module k (A i)] (B : ∀ i, Submodule k (A i)) (l : k) (e : ι → ℕ),
    (∀ i, LatIncl l (B i) (e i)) → ∀ y : ⨂[k] i, A i, l ^ (∑ i, e i) • y ∈ tensSub B

end Formalism.RankGapBounds.FormsTensorLocalization
