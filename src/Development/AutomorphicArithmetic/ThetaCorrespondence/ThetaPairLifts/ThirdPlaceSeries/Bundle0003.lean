module

public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AllCuspidalOpenBound
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.SumRepresentations
namespace At
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
section RepOps
variable {Γ : Type} [Group Γ] {k : Type} [CommRing k]
end RepOps
def provisionFortyOne (i : N.Loc) : Prop :=
  ((∃ rq : N.X i → (Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin R.nV) (Qbar (N.l i))), ∀ x, IsHeckeGaloisQ N A i x (rq x)) ∧
    ∃ r, GoodR N i r) ∧
  (∀ P P' : A.AV i, A.ptV i P ≠ none → A.ptV i P = A.ptV i P' →
    (∀ Pa Pa', IsBCV N A i P Pa → IsBCV N A i P' Pa' → Pa.Perm Pa') ∧
    ∀ w, w ∉ N.S i → w ∉ N.Q i →
      (IsSplitPl H w → A.locV i P w = A.locV i P' w) ∧
      (¬ IsSplitPl H w → ubc R.nV (A.satV i P w) = ubc R.nV (A.satV i P' w))) ∧
  ∀ r, GoodR N i r → G1 N i r ∧ _root_.UpperTheory.GalS.G2a N A i r ∧ _root_.UpperTheory.GalS.G3 N i r ∧ G4 N i r
end At
open Formalism.BasicNotions
def adm2_alt (D : D7) : Prop := _root_.UpperTheory.GalS.AutomorphicGaloisAdmissible D.nd D.naut
def adm7_alt (D : D7) : Prop := _root_.UpperTheory.GalN.AllCuspidalOpenBound D.nd D.naut
def provisionFortyOne (D : D7) : Prop := ∀ i, _root_.Formalism.MainNotions.SumRepresentations.At.provisionFortyOne D.nd D.naut i
def CuspidalGaloisUnramified' (D : D7) : Prop := ∀ i, _root_.UpperTheory.GalS.UnusedSlot55 D.nd D.naut i
def provisionFirst (D : D7) : Prop := _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D ∧ _root_.Formalism.MainNotions.SumRepresentations.CuspidalGaloisUnramified' D ∧ Conclusion42 D
def AdmAAlt (D : D7) : Prop := tie0 D ∧ hypO D ∧ adm1 D ∧ _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D
def AdmAtAlt (D : D7) : Prop := _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D ∧ _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D
def AdmissibleDatum (D : D7) : Prop := _root_.Formalism.MainNotions.SumRepresentations.AdmAtAlt D ∧ adm6 D ∧ adm8 D
end Formalism.MainNotions.SumRepresentations
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.AdmissibleParameterJ
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual NumberField IsDedekindDomain
variable {D : D7}
section Sets
variable (D)
end Sets
section Emb
variable (D)
variable {D}
end Emb
section Stmt
variable (D)
variable {D} (L : SizeData₂ D)
end Stmt
section admitted
variable (D)
def DeRhamFamilyAwayAlt : Prop := ∀ i r, GoodR D.nd i r → _root_.UpperTheory.GalS.G2a D.nd D.naut i r
variable {D} (L : SizeData₂ D)
def AdmJAlt : Prop :=
  _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D ∧ CrysIffWD D.nd D.naut ∧ _root_.UpperTheory.GalS.DeRhamJumpsDistinctCondition D ∧ AdmDict D ∧ AdmRead D ∧ AdmPar L
variable (D) in
def JumpClosed : Prop := ∀ L : SizeData₂ D, _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L → JumpConditions L
end admitted
end Formalism.MainNotions.AdmissibleParameterJ
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameSum
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
def TameSumAlt (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)), (∃ x, HasParamX D.nd D.naut i x Sig) → _root_.UpperTheory.GalS.FullLabS D Sig →
    IsCuspIso D.nd D.naut Sig →
    ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsRepOfSig D.nd D.naut i Sig ρ →
    ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → TameFixed D i Sig ρ k ∧
      ∀ w ∈ placesOver D.host.E (D.host.g k), TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) → TameAnyAt D i Sig ρ k w
end GlobalTheory.TypeLeaf
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TheoremThreePrimeStatement
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.AdmissibleThreePrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
def Adm3PVariant (D : D7) : Prop := SumRepresentations.tieLab D ∧ _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues D
def ThreePrimeTheoremStatement (D : D7) : Prop := _root_.Formalism.MainNotions.AdmissibleThreePrime.Adm3PVariant D → TheoremThreePrime D
end Formalism.MainNotions.AdmissibleThreePrime
end
end
end

