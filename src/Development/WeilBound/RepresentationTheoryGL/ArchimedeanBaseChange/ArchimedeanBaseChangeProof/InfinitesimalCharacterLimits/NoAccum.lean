module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.GalStepOfHyp
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TreeParts

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E

namespace PositivityTheory.Rg.BcB.SpectralAccumulation

attribute [local instance] borelH

def IsCuspD {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (V : Submodule ℂ (Sm E N)) : Prop :=
  IsDiscrete V ∧ ∀ φ ∈ V, ∀ r, 0 < r → r < N → Exp r φ.1 = ∅

def LimAt (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (W₁ : Submodule ℂ (Kinf E a → ℂ))
    (W₂ : Submodule ℂ (Kinf E b → ℂ)) (Ω₁ Ω₂ : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)))
    (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (Θ₁ Θ₂ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) : Prop :=
  ∀ (D : Dom E a b) (ι : Type) [Fintype ι] (M : ℕ)
  (m₁ : ℕ → (E →+* ℂ) → Multiset ℂ) (m₂ : ℕ → (E →+* ℂ) → Multiset ℂ) (n₁ n₂ : (E →+* ℂ) → Multiset ℂ)
  (C : Set (HeckeM E a b ι)) (lam : ℕ → HeckeM E a b ι → ℂ) (lam₀ : HeckeM E a b ι → ℂ)
  (f : ℕ → ι → H E a b → ℂ), C.Countable →

  (∀ (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (ν : Measure (GA E N)) [ν.IsHaarMeasure]
    (K' : Subgroup (GL (Fin N) (Af E))) (W' : Submodule ℂ (Kinf E N → ℂ)) (R' : ℝ),
    IsOpen (K' : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W' → Repro ν K' W' R') →

  (∀ k i, Continuous (f k i)) → (∀ k, f k ≠ 0) → (∀ k, LeftInv (f k)) → (∀ k, WL2 D M (f k)) →
  (∀ k i, TypeH K₁ K₂ W₁ W₂ (f k i)) →
  (∀ k i (m₂ : GA E b), ∃ φ : Sm E a, φ.1 = fun x => f k i (x, m₂)) →
  (∀ k i (m₁ : GA E a), ∃ φ : Sm E b, φ.1 = fun x => f k i (m₁, x)) →
  (∀ k, ∀ φ ∈ slices₁ (f k), IsAutForm φ) → (∀ k, ∀ φ ∈ slices₂ (f k), IsAutForm φ) →
  (∀ k τ, HasInfCharGL (Submodule.span ℂ (slices₁ (f k))) τ (m₁ k τ)) →
  (∀ k τ, HasInfCharGL (Submodule.span ℂ (slices₂ (f k))) τ (m₂ k τ)) →
  (∀ k, ∀ h ∈ C, heckeAct h (f k) = lam k h • f k) →

  (∀ τ (ε : ℝ), 0 < ε → ∀ᶠ k in atTop, MClose ε (m₁ k τ) (n₁ τ) ∧ MClose ε (m₂ k τ) (n₂ τ)) →
  RealSym n₁ → RealSym n₂ → (∀ τ, GapM (n₁ τ) ∧ GapM (n₂ τ)) →
  (∀ h ∈ C, Tendsto (fun k => lam k h) atTop (𝓝 (lam₀ h))) →
  ∃ (s₁ : Tr E a) (s₂ : Tr E b) (F : ι → H E a b → ℂ), s₁.Good ∧ s₂.Good ∧ s₁.Untw ∧ s₂.Untw ∧
    s₁.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₁ M, ∃ W' ∈ Ω₁ M, HasType K' W' V) ∧
    s₂.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₂ M, ∃ W' ∈ Ω₂ M, HasType K' W' V) ∧
    (∀ τ, HasInfCharGL s₁.space τ (n₁ τ)) ∧ (∀ τ, HasInfCharGL s₂.space τ (n₂ τ)) ∧
    F ≠ 0 ∧ (∀ i, F i ∈ pairSpace s₁.space s₂.space) ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (F i)) ∧
    ∀ h ∈ C, heckeAct h F = lam₀ h • F

end PositivityTheory.Rg.BcB.SpectralAccumulation

end
