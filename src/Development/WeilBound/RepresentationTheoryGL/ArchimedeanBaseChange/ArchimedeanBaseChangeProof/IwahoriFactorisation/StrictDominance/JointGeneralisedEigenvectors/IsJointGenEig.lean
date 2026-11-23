module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistedIndependenceLemma.TwistedIndependence

@[expose] public section

noncomputable section

open GlobalTheory.PRep

namespace PositivityTheory.SphericalProduct

structure CassData (G : Type) [Group G] [TopologicalSpace G] where

  N : Subgroup G

  Nm : Subgroup G

  T : Subgroup G

  J : Subgroup G
  isOpen_J : IsOpen (J : Set G)
  isCompact_J : IsCompact (J : Set G)
  isClosed_N : IsClosed (N : Set G)
  isClosed_Nm : IsClosed (Nm : Set G)
  isClosed_alt : IsClosed (T : Set G)
  norm_N : ∀ t ∈ T, t ∈ Subgroup.normalizer (N : Set G)
  norm_Nm : ∀ t ∈ T, t ∈ Subgroup.normalizer (Nm : Set G)

  fact_low : ∀ x ∈ J, ∃ a ∈ J ⊓ Nm, ∃ b ∈ J ⊓ T, ∃ c ∈ J ⊓ N, x = a * b * c

  fact_up : ∀ x ∈ J, ∃ c ∈ J ⊓ N, ∃ b ∈ J ⊓ T, ∃ a ∈ J ⊓ Nm, x = c * b * a

variable {G : Type} [Group G] [TopologicalSpace G]

namespace CassData

def JT (D : CassData G) : Subgroup D.T := D.J.comap D.T.subtype

def IsDom (D : CassData G) (t : D.T) : Prop :=
  (∀ n ∈ D.J ⊓ D.N, (t : G) * n * (t : G)⁻¹ ∈ D.J ⊓ D.N) ∧
  (∀ n ∈ D.J ⊓ D.Nm, (t : G)⁻¹ * n * (t : G) ∈ D.J ⊓ D.Nm) ∧
  (∀ x ∈ D.J ⊓ D.T, (t : G) * x * (t : G)⁻¹ ∈ D.J ⊓ D.T ∧ (t : G)⁻¹ * x * (t : G) ∈ D.J ⊓ D.T)

def IsStrDom (D : CassData G) (t : D.T) : Prop :=
  D.IsDom t ∧ (∀ n ∈ D.N, ∃ j : ℕ, (t : G) ^ j * n * ((t : G) ^ j)⁻¹ ∈ D.J ⊓ D.N) ∧
    ∀ U : Set G, IsOpen U → (1 : G) ∈ U → ∃ j : ℕ, ∀ n ∈ D.J ⊓ D.Nm, ((t : G) ^ j)⁻¹ * n * (t : G) ^ j ∈ U

def piN (D : CassData G) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) :
    Representation ℂ D.T (Jacquet π D.N) :=
  jacquet π D.N D.T.subtype (fun m => D.norm_N m m.2)

abbrev proj (D : CassData G) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (v : V) :
    Jacquet π D.N :=
  Submodule.Quotient.mk v

end CassData

open CassData

variable (G) [IsTopologicalGroup G]

def A1 : Prop :=
  ∀ (D : CassData G) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π →
    ∀ t t' : D.T, D.IsDom t → D.IsDom t' → ∀ U U' : Module.End ℂ (fixed π D.J),
      PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → PositivityTheory.Lbc.IsHeckeOpG π D.J (t' : G) U' →
      PositivityTheory.Lbc.IsHeckeOpG π D.J ((t : G) * t') (U * U')

def A2 : Prop :=
  ∀ (D : CassData G) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π →
    ∀ t : D.T, D.IsDom t → ∀ U : Module.End ℂ (fixed π D.J), PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U →
      ∀ v : fixed π D.J, D.proj π ((U v : fixed π D.J) : V) = D.piN π t (D.proj π (v : V))

def A4 : Prop :=
  ∀ (D : CassData G) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π →
    (∃ t : D.T, D.IsStrDom t) →
    (∀ v : fixed π D.J, D.proj π (v : V) ∈ fixed (D.piN π) D.JT) ∧
    ∀ w ∈ fixed (D.piN π) D.JT, ∃ v : fixed π D.J, D.proj π (v : V) = w

end PositivityTheory.SphericalProduct

end
