module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

noncomputable section

namespace GlobalTheory.SWQ

open scoped TensorProduct NNReal ENNReal
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

def qd (R : Type) [CommRing R] [Algebra F R] (a : Fin N → F) (u : Fin N → R) : R :=
  ∑ l, algebraMap F R (a l) * u l ^ 2

def Bd (R : Type) [CommRing R] [Algebra F R] (a : Fin N → F) (u u' : Fin N → R) : R :=
  ∑ l, algebraMap F R (2 * a l) * u l * u' l

def rat (ξ : Fin N → F) : Fin N → AF F := fun l => algebraMap F (AF F) (ξ l)

def inf (u : Fin N → AF F) : Fin N → Ainf F := fun l => fstA F (u l)

def fin (u : Fin N → AF F) : Fin N → Af F := fun l => sndA F (u l)

def re (x : Ainf F) (w : InfinitePlace F) : ℝ :=
  (InfinitePlace.Completion.extensionEmbedding w (x w)).re

def sz (u : Fin N → AF F) : ℝ := ∑ l, ∑ w : InfinitePlace F, |re (inf u l) w|

def hf (F : Type) [Field F] [NumberField F] : AF F := pairA F (algebraMap F (Ainf F) (1 / 2)) 1

def Decay (Φ : (Fin N → AF F) → ℂ) : Prop :=
  Continuous Φ ∧ (∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ u, fin u ∉ K → Φ u = 0) ∧
    ∀ k : ℕ, ∃ C : ℝ, ∀ u, ‖Φ u‖ * (1 + sz u) ^ k ≤ C

def IsCov1 (ν : Measure (AF F)) : Prop :=
  ν.IsAddHaarMeasure ∧ ∃ D : Set (AF F), MeasurableSet D ∧
    IsAddFundamentalDomain (algebraMap F (AF F)).range.toAddSubgroup D ν ∧ ν D = 1

def muV (N : ℕ) (ν : Measure (AF F)) : Measure (Fin N → AF F) := Measure.pi fun _ => ν

def IsLam (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) : Prop :=
  (∀ w, lam w ≠ 0) ∧ ∀ x : Ainf F,
    psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, lam w * re x w : ℝ) : ℂ))

def Ctx (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F) : Prop :=
  IsTotallyReal F ∧ IsCharAF F ψ ∧ IsLam ψ lam ∧ IsCov1 ν ∧ ∀ l, a l ≠ 0

variable (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F)

def Ub (b : AF F) (Φ : (Fin N → AF F) → ℂ) : (Fin N → AF F) → ℂ := fun u => ψ (b * qd (AF F) a u) * Φ u

def Da (t : AF F) (Φ : (Fin N → AF F) → ℂ) : (Fin N → AF F) → ℂ := fun u => Φ (t • u)

def Fo (Φ : (Fin N → AF F) → ℂ) : (Fin N → AF F) → ℂ :=
  fun u => ∫ s, Φ s * ψ (Bd (AF F) a s u) ∂(muV N ν)

def rho (x y : Fin N → AF F) (Φ : (Fin N → AF F) → ℂ) : (Fin N → AF F) → ℂ :=
  fun u => ψ (Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y) * Φ (u + x)

def th (Φ : (Fin N → AF F) → ℂ) : ℂ := ∑' ξ : Fin N → F, Φ (rat ξ)

variable {ψ a}

section Herm

variable {E : Type} [Field E] [Algebra F E] {M : ℕ}

end Herm

theorem decay_zero : Decay (fun _ : Fin N → AF F => (0 : ℂ)) :=
  ⟨continuous_const, ⟨∅, isCompact_empty, fun _ _ => rfl⟩, fun _ => ⟨0, fun _ => by simp⟩⟩

end GlobalTheory.SWQ
