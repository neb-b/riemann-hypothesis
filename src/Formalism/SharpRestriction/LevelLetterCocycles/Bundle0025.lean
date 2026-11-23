module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0022
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseCoefJumpProof
public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0021
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0023
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PsiLowerBoundHolds
public import Formalism.SharpRestriction.LevelLetterCocycles.SplitROfSteps
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.LinearIndependentSmulOfNeZero
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.BaseChangeEveryTheory
section
namespace Formalism.MainNotions.UnusedSlot80

open Formalism.BasicNotions

theorem base_change_statement (D : D7) : H1fBaseChangeTheorem D := BCF.base_change_statement_of_jump Formalism.MainNotions.N.GlobalTheory.coefficient_jump_general D

theorem base_change_every_theory (Th : LocTheory) : Formalism.MainNotions.WachCoordinates.admBC Th := BCF.base_change_of_coefficient_jump Formalism.MainNotions.N.GlobalTheory.coefficient_jump_general Th

end Formalism.MainNotions.UnusedSlot80
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ClassMapStep
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

def InvLiftStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → invLiftR D HW

def ClassMapStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → classMapR D HW

def FrameStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → frameR D HW

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.CylinderCountFamily
section
noncomputable section

namespace Formalism.MainNotions.ArithmeticCylinders

open Formalism.BasicNotions Formalism.MainNotions Filter Topology Polynomial

structure AllRowsAt (D : D7) (Dall Dgood : ℕ) : Type 1 where
  B : Formalism.MainNotions.S.RowsAut
  n_eq : B.I.n = D.R.r
  f_eq : B.I.f = D.R.f
  labAll : ∀ k, Fin Dall → D.nd.PlG k → (ZMod (D.host.g k))[X]
  labAll_label : ∀ k σ v, IsLabel D k (labAll k σ v)
  inc : Fin Dgood → Fin Dall
  eVec : ∀ k, D.nd.PlG k → MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))
  eVec_idem : ∀ k v, eVec k v * eVec k v = eVec k v
  eT : Set (Tup2 D) → B.I.Gf → ℂ
  ReT : Set (Tup2 D) → (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
  ReT_spec : ∀ S, B.I.IsRConvF B.μf B.fund B.R (eT S) (ReT S)
  eT_univ : eT Set.univ = B.e
  ReT_univ : ReT Set.univ = B.Re
  eT_one : ∀ (k : Fin 2) (S : Finset (Tup D k)),
    (eT (cyl D k (S : Set (Tup D k))) 1).re =
      (B.e 1).re * ∑ t ∈ S, ∏ v, wtOf D k (eVec k v) (t v)

variable {D : D7} {Dall Dgood : ℕ}

def AllRowsAt.dimT (A : AllRowsAt D Dall Dgood) (S : Set (Tup2 D)) : ℕ :=
  A.B.I.Dcount A.B.σs A.B.μf A.B.fund A.B.R (A.ReT S)

def TieCountAt (A : AllRowsAt D Dall Dgood) (n₀ : ℕ) (Alev C₃ cb : ℝ) : Prop :=
  ∃ b h : ℝ,
    (∀ (k : Fin 2) (S : Set (Tup D k)),
      Formalism.MainNotions.PlaceDegreeData.HidaSetting A.B.I n₀ Alev b A.B.lam A.B.μf A.B.g (D.host.g (1 - k)) (A.eT (cyl D k S)) ∧
      Formalism.MainNotions.PlaceDegreeData.CountData A.B.I A.B.lam A.B.σ A.B.w A.B.σs A.B.tens A.B.μf A.B.fund A.B.R
        (A.eT (cyl D k S)) (A.ReT (cyl D k S))) ∧
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (A.B.I.ε v) (A.B.lam v) h) ∧
    C₃ * (A.B.I.n : ℝ) ^ 19 * (A.B.I.f : ℝ) ^ 5 * Real.log (b * A.B.I.rd) ≤ h ∧
    Real.log (A.B.I.f : ℝ) ≤ Real.sqrt (A.B.I.n : ℝ) ∧
    Real.log (Real.log b) ≤ cb * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ) ∧
    0 < A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund A.B.e

variable (D)

def AllRows.toAt {D : D7} (A : AllRows D) : AllRowsAt D D.what₂.Dall D.what₂.Drows where
  B := A.B
  n_eq := A.n_eq
  f_eq := A.f_eq
  labAll := A.labAll
  labAll_label := A.labAll_label
  inc := A.inc
  eVec := A.eVec
  eVec_idem := A.eVec_idem
  eT := A.eT
  ReT := A.ReT
  ReT_spec := A.ReT_spec
  eT_univ := A.eT_univ
  ReT_univ := A.ReT_univ
  eT_one := A.eT_one

end Formalism.MainNotions.ArithmeticCylinders

namespace Formalism.MainNotions.N.CylinderCountFamily

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.FamilyNumericLemmas Filter Topology Polynomial

end Formalism.MainNotions.N.CylinderCountFamily
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantUniformizer
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def GenStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → genR D

def LiftStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → liftR D

def NormStep : Prop := ∀ D : D7, normR D

def DvdStep : Prop := dvdR

def QuotStep : Prop := ∀ D : D7, adm8 D → adm11 D → quotR D

def DeltaInvariantUniformizer : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    adm1 D HW F Cm → p9R D HW

def ExtStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → extOfR D HW

def WStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → wKillR D HW

def KerLamStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → FontExAll D HW F → kerLamR D HW

def NinLamStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → ninLamR D HW

def GradNStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → gradNR D HW

def FrobPiNStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → frobPiNR D HW

def GamPiStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → gamPiR D HW

def OneGenStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → oneGenR D HW

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ExistsGoodPlacesEveryConjugate
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.MainNotions.N.TwAll

section Conj

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem psiAt_side_zpow {Γ A : Type} [Group Γ] [CommGroup A] (b b' : Bool) (ψ : Γ →* A) (a : ℤ) :
    ∃ a' : ℤ, a'.natAbs = a.natAbs ∧ Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b' (ψ ^ a) = Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ ^ a') := by
  cases b <;> cases b'
  · exact ⟨a, rfl, rfl⟩
  · refine ⟨-a, Int.natAbs_neg a, ?_⟩
    simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, zpow_neg]
  · refine ⟨-a, Int.natAbs_neg a, ?_⟩
    simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, zpow_neg]
  · exact ⟨a, rfl, rfl⟩

end Conj

end Formalism.MainNotions.N.TwAll

namespace Formalism.MainNotions

open Formalism.MainNotions.N.TwAll

def TwGoodAll (D : D7) (I : TwIn D) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : Prop :=
  ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) → TwGoodOne D I i b Q k' (ψ ^ a)

def rawPack {D : D7} (C : NChoice D) (w : D.what₂.places.Pl) : TwPack D := ⟨C.twI w, C.Q w, C.k' w, C.psi' w⟩

def IntegralHeckeEveryConjugate (D : D7) (bkP : BlochKatoReduction.BK D) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.pin bkP) i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.FullRk D.nexp E i j b (IntegralHeckeForms.SgJ D.nexp E i j b)) →
    ∀ S : ∀ (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b),
      (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.BasisOf D.nexp i j b (IntegralHeckeForms.SgJ D.nexp E i j b) (S j b)) →
    ∀ A : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ),
      ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) →
        IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.pin bkP) E N0 i eps' S A Q k' (ψ' ^ a)

end Formalism.MainNotions

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section Kill

variable {D : D7} (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

end Kill

end Formalism.MainNotions.N.KillingConditions

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section C6

variable {D : D7} (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

end C6

end Formalism.MainNotions.N.KillingConditions

namespace Formalism.MainNotions.LatticeVariant

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (psiAt nval SetHyp PsiOk partA partAT partC partD)
open scoped TensorProduct

section All

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}



end All

end Formalism.MainNotions.LatticeVariant

namespace Formalism.MainNotions.IntegralHeckeForms

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

section All

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}


variable (Y) in
def goodTwistExistsAllCoprimePowers (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X) (E : ExpDat Y) (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, FullRk Y E i j b (SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, BasisOf Y i j b (SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    ∀ a : ℤ, a.natAbs.Coprime (X.l i) → GoodTw Y bkP E N0 i eps' S A Q k' (ψ' ^ a)

end All

end Formalism.MainNotions.IntegralHeckeForms

namespace Formalism.MainNotions

end Formalism.MainNotions

namespace Formalism.MainNotions.N.TwAll

open Formalism.MainNotions.BlochKatoReduction.Gen (nval)

section Tame

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}

end Tame

end Formalism.MainNotions.N.TwAll

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.MainNotions.N.TwAll

section DensityAveraging

variable {D : D7}

end DensityAveraging

end Formalism.MainNotions.N.KillingConditions

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FinLev
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def FinLev (W : LocWach PD LL O v n) : Prop :=
  ∀ (a : ZMod n) (e : ℕ) (H : ℕ → ℕ), ∃ D : ℕ, ∀ u ∈ W.AΔ, ∃ (c : Fin D → O) (w : LetA O n),
    w ∈ W.AΔ ∧ (letE a : LetA O n) * u =
      letE a * ∑ j : Fin D, algebraMap O (LetA O n) (c j) * W.π₀ ^ (j : ℕ) +
        W.π₀ * (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ H t) ^ 2 * (letE a * w)

end Formalism.MainNotions.UnusedSlot80.UGen
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FirstFrameStepImplication
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

def KapPiStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → kapPiR D HW

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LemCStep
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def LemC (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' S : ℕ) (up : (K →ₐ[Qp] LL) → Bool) (b : (K →ₐ[Qp] LL) → ℕ) (c : ZMod n) : Prop :=
  ∀ x (hx : x ∈ NcS W T (c - 1)), (∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c → up τ = true →
    x ∈ FilL W T Pt c τ (b τ)) → ∀ f, IsCoord W Pt π' Eπ h' S up b c f →
    f ⊗ₜ mkL W T π' c x hx ∈ InvL W T Pt π' Eπ h' c ⊤

end Local

section Record

end Record

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionRingInput
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

def SecondPropositionHypothesis : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → u2R D HW

end Formalism.MainNotions.N.Ln34

end
end

