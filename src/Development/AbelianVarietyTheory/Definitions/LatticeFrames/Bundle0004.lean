module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
public import Formalism.LocalRingCardinality.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.HermCoord
section
noncomputable section

namespace GlobalTheory.SWC

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

section Local

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)

def starM {n : ℕ} (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E) := (g.map (sigR R σ)).transpose

def hermCoord {n : ℕ} (S : HermR R σ n) : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
  (fun a => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (S.1 a a), fun p => S.1 p.1.1 p.1.2)

variable [TopologicalSpace R] {M n : ℕ}

end Local

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  {d : ℕ} {b : Module.Basis (Fin d) F E} {M n : ℕ}

end Global

end GlobalTheory.SWC

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
section
noncomputable section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2
namespace GlobalTheory.Core.Deg

def HypL (D : D7) (L C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  let k : ℝ := D.R.k
  let m : ℝ := D.R.m
  let f : ℝ := D.R.f
  let n : ℝ := D.R.r
  let r : ℝ := D.R.rS
  let b : ℝ := Real.exp L
  let Del : ℝ := D.s.Del
  let g1 : ℝ := D.host.g 0
  let g2 : ℝ := D.host.g 1
  1 < L ∧ C' * m ^ 5 * f * L ≤ k ∧
  D.R.m ^ 4 ≤ D.R.f ∧ D.R.f ≤ D.R.k ∧
  Real.log f ≤ Real.sqrt r ∧
  Cl * L ≤ f * Real.log k ∧
  Cl * (m ^ 2 * L) ≤ k ∧
  (∀ τ j, 1 ≤ j → j ≤ D.R.m → Cl * (m * k * Del) ≤ bOne D τ j) ∧
  Cl * (m * Real.log D.host.v) ≤ k ∧
  Cl * (m ^ 3 * L * Real.log D.host.rdE) ≤ k * Real.log k ^ 2 ∧
  Real.log D.host.rdE ≤ L / Cl ∧
  (k * b) ^ 8 ≤ g1 ∧ g1 ≤ b ^ Cg ∧ (k * b) ^ 8 ≤ g2 ∧ g2 ≤ b ^ Cg ∧
  (∀ τ j, 1 ≤ j → j ≤ D.R.m → max (k ^ Cl) (b ^ cb) ≤ bOne D τ j ∧ bOne D τ j ≤ b ^ (2 : ℝ)) ∧
  (∀ τ, bOne D τ D.R.m ≤ 2 * bOne D τ 1) ∧
  (∀ u τ, uOne D u τ 1 ≤ b ^ Cu) ∧
  1 ≤ D.host.v ∧
  (k * f * L) ^ Cl ≤ Del ∧
  (∀ τ j, 1 ≤ j → j + 1 ≤ D.R.m → Cl * n ^ 19 * f ^ 5 * L ≤ bOne D τ (j + 1) - bOne D τ j) ∧
  (∀ τ (i : Fin D.R.r) (h : i.1 + 1 < D.R.r),
    Cl * k * m ^ 4 + n * m ^ 10 < lamS D.R (D.hc τ) i - lamS D.R (D.hc τ) ⟨i.1 + 1, h⟩) ∧
  (∀ u, b ^ (cT * m) ≤ Tr D u ∧ Tr D u ≤ b ^ (CT * m)) ∧
  Cl ≤ m ∧ 0 < Cl

def DataNW (D : D7) : Prop :=
  let k : ℝ := D.R.k
  let Del : ℝ := D.s.Del
  (∀ τ l, 1 ≤ l → l ≤ D.R.k - 1 → 0 ≤ vOne D τ l ∧ vOne D τ l ≤ 4 * k * Del) ∧
  (∀ u (l : ℕ), 1 ≤ l → l ≤ D.R.k - 2 →
    (∀ τ, uOne D u τ (l + 1) = vOne D τ l - 1 / 2) ∨ (∀ τ, uOne D u τ (l + 1) = vOne D τ l - 1 / 2 - Del)) ∧
  (∀ u τ, 4 * k * Del ≤ uOne D u τ 1 - vOne D τ 1) ∧
  (∀ u τ, ¬ IsTop D τ → uOne D u τ 1 - vOne D τ 1 ≤ 8 * k * Del) ∧
  (∀ u τ, ¬ IsTop D τ → uOne D u τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2) ∧
  (∀ τ, IsTop D τ → 3 ≤ bOne D τ 1 - bTop D τ ∧ bOne D τ 1 / 2 ≤ bTop D τ) ∧
  (∀ u τ, InterlaceS (show D.R.k ≤ D.R.r by have := D.R.two_le_m; unfold Formalism.BasicNotions.Ranks.r; omega)
    (uS D u τ) (lamS D.R (D.hc τ))) ∧
  (∀ u u', u ≠ u' → ∀ τ, uS D u τ ≠ uS D u' τ) ∧
  (∀ u, SplitsE D (D.mem u).A.T ∧
    (D.mem u).A.T % (D.host.g 0 * D.host.g 1) ^ 2 = 1 % (D.host.g 0 * D.host.g 1) ^ 2) ∧
  (∀ u, 0 < D.duS u) ∧
  SplitsE D (D.host.g 0) ∧ SplitsE D (D.host.g 1) ∧
  NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 ∧
  (∀ u, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)
section At
variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

def VanishingGramTermsBound : Prop :=
  Summable ((Y.tO u u).degSet.indicator (fun t => ‖(Y.tO u u).op t‖)) ∧
    ‖(Y.tO u u).part (Y.tO u u).degSet‖ ^ 2 ≤ duC X Y u * epsK D

end At

def Led (Q : ∀ {D : D7} {X : HidaSetting D}, Full X → D.what₂.Word → Prop) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (_ : SIso D.s (sOf hF)) (u : D.what₂.Word),
      Formalism.BasicNotions.Ties D → Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → DataNW D → ConcTie X Y →
      (Y.tO u u).AbsConv → Q Y u

def Win (Q : ∀ {D : D7} {X : HidaSetting D}, Full X → D.what₂.Word → Prop) : Prop :=
  ∀ Cg cb Cu cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (_ : SIso D.s (sOf hF)) (u : D.what₂.Word),
      Formalism.BasicNotions.Ties D → Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D → Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y →
      (Y.tO u u).AbsConv → Q Y u

def VanishingGramTermsBoundParams : Prop := Led VanishingGramTermsBound

def VanishingGramTermsBoundWindow : Prop := Win VanishingGramTermsBound

theorem hypL_of {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) :
    HypL D large₂.sc.L C' Cl Cg cb Cu cT CT :=
  ⟨Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos, h.2⟩

end GlobalTheory.Core.Deg
end
end

