module

public import Mathlib
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0007
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.HermitianLattices.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.AdmissibleBoundsFromSource

export Formalism.MainNotions.S.UnitaryVolumeMass (f3 Kpp)

open Formalism.BasicNotions Formalism.MainNotions.S NumberField IsDedekindDomain
open scoped InnerProductSpace nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Letters

variable (D : D7) (large₂ : SizeData₂ D)

def Gam : ℝ := (D.mem D.u₀).A.GamP

def du (u : D.what₂.Word) : ℝ := D.duS u

def Dall : ℝ := D.what₂.Dall

def Dst : ℝ := D.what₂.Dstar

def eta0 : ℝ := large₂.sc.b ^ (-(6 : ℝ))

def xK : ℝ := Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k))
end Letters

section Hyp

variable (D : D7) (large₂ : SizeData₂ D)

def hyp (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  StandingNumericalData D C0 ∧ StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ 1 ≤ C0

def DiagonalKernelBoundParameters (Cl Cg CT : ℝ) : Prop :=
  UnitaryVolumeMass.KTwoParameterConditions D large₂ Cl Cg CT

def WordPairStandingData (u u' : D.what₂.Word) : Prop :=
  1 ≤ D.R.rS ∧
  (Lat.Tu D u).Prime ∧ (Lat.Tu D u').Prime ∧ 3 ≤ Lat.Tu D u ∧ 3 ≤ Lat.Tu D u' ∧
  Lat.SplitsCompletely (E := D.host.E) (Lat.Tu D u) ∧ Lat.SplitsCompletely (E := D.host.E) (Lat.Tu D u') ∧
  (D.host.g 0).Prime ∧ (D.host.g 1).Prime ∧ D.host.g 0 ≠ D.host.g 1 ∧
  (∀ i, Lat.SplitsCompletely (E := D.host.E) (D.host.g i)) ∧
  Nat.Coprime (Lat.gS D) (Lat.Tu D u * Lat.Tu D u') ∧ Lat.Tu D u ≡ Lat.Tu D u' [MOD Lat.gS D]

def WordPairParameters (u u' : D.what₂.Word) (Cl A : ℝ) : Prop :=
  WordPairStandingData D u u' ∧
  Tr D u' / Tr D u ≤ A ∧ Tr D u / Tr D u' ≤ A ∧
  Cl * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) ≤ (D.R.k : ℝ) * Real.log D.R.k ∧
  Real.log (D.R.f : ℝ) ^ 2 ≤ A * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) ∧
  Real.log (D.R.f : ℝ) ≤ A * (D.R.rS : ℝ) ^ 2 ∧
  ∀ τ, vand (uS D u' τ) ≤ A ^ D.R.k * vand (uS D u τ) ∧ vand (uS D u τ) ≤ A ^ D.R.k * vand (uS D u' τ)

def CountTheoremHypotheses (n0 : ℕ) (A C cb : ℝ) : Prop :=
  NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 ∧
  n0 ≤ D.R.r ∧ (D.R.rS + 1) ^ 2 ≤ D.R.r ∧
  Real.log (Real.log D.host.rdE) ≤ (D.R.r : ℝ) ∧
  (∀ (τ : D.what₂.Tau) (i : Fin D.R.r), |lamS D.R (D.hc τ) i| ≤ large₂.sc.b ^ 2) ∧
  gg D ≤ large₂.sc.b ^ A ∧ 4 * D.R.r < D.host.g 0 ∧ SplitsE D (D.host.g 0) ∧
  (∀ τ : D.what₂.Tau, Formalism.QuantumDeterminants.GapAtLeast (epsS D.R) (lamS D.R (D.hc τ))
    (C * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * Real.log (large₂.sc.b * D.host.rdE))) ∧
  Real.log (D.R.f : ℝ) ≤ Real.sqrt (D.R.r : ℝ) ∧ 2 ≤ large₂.sc.b ∧
  Real.log (Real.log large₂.sc.b) ≤ cb * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ)

end Hyp

structure AdmC where

  A5 : ℝ
  cL : ℝ

  cN : ℝ
  CN : ℝ

  CE : ℝ

  CA : ℝ
  CA' : ℝ
  Ce : ℝ

  n7 : ℕ
  A7 : ℝ
  C7 : ℝ
  cb7 : ℝ
  c7 : ℝ

  ep0 : ℝ
  CV : ℝ

  C1 : ℝ
  C2 : ℝ
  c5 : ℝ

section admitted

variable (D : D7) (large₂ : SizeData₂ D)

def adm1 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → UnitaryVolumeMass.cExp D

def adm2 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → UnitaryVolumeMass.cIdOne D

def adm3 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → DiagonalKernelBoundParameters D large₂ Cl Cg CT → UnitaryVolumeMass.cK2off D

def ArchimedeanSignatureMatching (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → UnitaryVolumeMass.c2aG D

def adm5 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → DiagonalKernelBoundParameters D large₂ Cl Cg CT →
    ∀ u : D.what₂.Word, hsNormSq (Kpp D u u) ≤ du D u * xK D

def adm6 (C0 C' Cl Cg cb Cu cT CT A c : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → ∀ u u' : D.what₂.Word, WordPairParameters D large₂ u u' Cl A → UnitaryVolumeMass.LoopPairSumBound D u u' c

def adm7 (C0 C' Cl Cg cb Cu cT CT c C : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → UnitaryVolumeMass.NonGenericKernelBound D large₂ c C

def adm8 (C0 C' Cl Cg cb Cu cT CT C : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → UnitaryVolumeMass.GenericScalarPairSum D large₂ C

def adm9 (C0 C' Cl Cg cb Cu cT CT CA CA' Ce : ℝ) : Prop :=
  let N : ℝ := NA D
  let r : ℝ := D.R.rS
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ u u' : D.what₂.Word, u ≠ u' → ∀ (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D),
    IsLocA D u u' x → IsLatGLOB D L →
    (∀ τ, IsCutS (uS D u τ) (uS D u' τ) (Set.Icc (x τ).a (x τ).b) ∧
      CA * ((D.R.k : ℝ) * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3) ≤ (x τ).b - (x τ).a ∧
      (x τ).a ≤ (x τ).a1 ∧ (x τ).b1 ≤ (x τ).b ∧ N ^ 3 / 2 ≤ (x τ).b1 - (x τ).a1) →
    (r + 1) * (CA / ThA D CA u u' x L) ^ (D.R.f : ℝ) ≤ 1 → CA' ≤ ThA D CA u u' x L →
    genScal D u u' ≤ (1 + CA * (r + 1) * (CA / ThA D CA u u' x L) ^ (D.R.f : ℝ)) * (1 + eSum D Ce) *
      f3 D * du D u * du D u' / Dst D

def adm10 (n0 : ℕ) (A C cb c : ℝ) : Prop := CountTheoremHypotheses D large₂ n0 A C cb →
  |Dall D - Dst D| ≤ Real.exp (-(c * D.R.r * D.R.f * Real.log D.R.r)) * Dst D

def WeylDimensionFormula (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ u τ, (dimPiU D.R.k (uS D u τ) : ℝ) = vand (uS D u τ) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)

def FilteredProjectionCriterion (C0 C' Cl Cg cb Cu cT CT ep0 : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ τ, (1 - ep0) * vand (lamSH D.R (D.hc τ)) ≤ VV D τ

def VandermondeUpperBound (C0 C' Cl Cg cb Cu cT CT C : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ τ, VV D τ ≤ Real.exp (C * D.R.k * D.R.m * large₂.sc.L) * vand (lamSH D.R (D.hc τ))

def adm11 (C0 C' Cl Cg cb Cu cT CT ep0 C : ℝ) : Prop :=
  WeylDimensionFormula D large₂ C0 C' Cl Cg cb Cu cT CT ∧ FilteredProjectionCriterion D large₂ C0 C' Cl Cg cb Cu cT CT ep0 ∧
    VandermondeUpperBound D large₂ C0 C' Cl Cg cb Cu cT CT C

def adm12 : Prop := Formalism.HermitianLatticesTheory.SiegelMassRatio

def adm13 (C0 C' Cl Cg cb Cu cT CT C1 C2 c5 CA : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  UnitaryVolumeMass.cTvA D ∧ UnitaryVolumeMass.cTvB D C1 ∧ UnitaryVolumeMass.cTvC D C2 ∧ UnitaryVolumeMass.cTvF D large₂ c5 CA

def adm14 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ u u' : D.what₂.Word,
    (∀ t : D.s.Term u u', ¬ D.s.relevant t → D.s.aTerm u u' t = 0) ∧
    (∀ t : D.s.Term u u', D.s.isId t → D.s.Gterm t = 0) ∧
    (∀ p : D.s.Pair u u', D.s.Gterm (D.s.pfst p) ≠ 0 → D.s.Gterm (D.s.psnd p) ≠ 0 → 1 ≤ D.s.s0 p)

def adm15 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ u u' : D.what₂.Word, Summable (fun p : D.s.Pair u u' => ‖D.s.pval p‖)

def fixAt (u : D.what₂.Word) (v : (D.mem u).A.vT) :
    Submodule ℂ ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :=
  (D.mem u).A.Mu0 ⊓ ⨅ c : ((D.mem u).A.Fv v)ˣ, LinearMap.ker ((D.mem u).A.rhoT v c - LinearMap.id)

def adm16 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ (u : D.what₂.Word) (v : (D.mem u).A.vT), (Module.finrank ℂ (fixAt D u v) : ℝ) = du D u / (Tr D u - 1)

def Adm1 (C0 C' Cl Cg cb Cu cT CT : ℝ) (ca : AdmC) : Prop :=
  adm1 D large₂ C0 C' Cl Cg cb Cu cT CT ∧ adm2 D large₂ C0 C' Cl Cg cb Cu cT CT ∧
    adm3 D large₂ C0 C' Cl Cg cb Cu cT CT ∧ ArchimedeanSignatureMatching D large₂ C0 C' Cl Cg cb Cu cT CT ∧ adm5 D large₂ C0 C' Cl Cg cb Cu cT CT ∧
    adm6 D large₂ C0 C' Cl Cg cb Cu cT CT ca.A5 ca.cL ∧ adm7 D large₂ C0 C' Cl Cg cb Cu cT CT ca.cN ca.CN ∧
    adm8 D large₂ C0 C' Cl Cg cb Cu cT CT ca.CE ∧ adm9 D large₂ C0 C' Cl Cg cb Cu cT CT ca.CA ca.CA' ca.Ce ∧
    adm11 D large₂ C0 C' Cl Cg cb Cu cT CT ca.ep0 ca.CV ∧ adm12 ∧
    adm13 D large₂ C0 C' Cl Cg cb Cu cT CT ca.C1 ca.C2 ca.c5 ca.CA ∧ adm14 D large₂ C0 C' Cl Cg cb Cu cT CT ∧
    adm15 D large₂ C0 C' Cl Cg cb Cu cT CT

def admitted (C0 C' Cl Cg cb Cu cT CT : ℝ) (ca : AdmC) : Prop :=
  Adm1 D large₂ C0 C' Cl Cg cb Cu cT CT ca ∧ adm10 D large₂ ca.n7 ca.A7 ca.C7 ca.cb7 ca.c7 ∧
    adm16 D large₂ C0 C' Cl Cg cb Cu cT CT

end admitted

section Conclusion₂

variable (D : D7) (large₂ : SizeData₂ D)

def Conclusion1 : Prop :=
  (∀ u u' : D.what₂.Word, u ≠ u' → Kpp D u u' = 0) ∧
  (∀ u, hsNormSq (Kpp D u u) ≤ du D u * xK D) ∧
  (∀ u u' : D.what₂.Word, u ≠ u' →
    hsNormSq (Kmat D.s u u' - Kpp D u u') ≤ (1 + eta0 D large₂) * du D u * du D u' / Dst D) ∧
  (∀ u, hsNormSq (Kmat D.s u u - Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) ≤
    Gam D * du D u ^ 2 / Dst D)

end Conclusion₂

structure GivC where
  C0 : ℝ
  Cg : ℝ
  cb : ℝ
  Cu : ℝ
  cT : ℝ
  CT : ℝ

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Family

end Formalism.MainNotions.AdmissibleBoundsFromSource
