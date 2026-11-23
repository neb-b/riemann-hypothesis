module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MainOf
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnitsInvHaar
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PRadicalTorusModulus

@[expose] public section

namespace CompanionTheory.SWFin

open NumberField GroundTheory.Automorphic Module GroundTheory.Heights₂.Heights.FiniteCovolume

universe u

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

section steps

variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (h : HermitianForm F E W) (v : Basis ι E W)

theorem te : TorusEmbedding.Statement h v :=
  TorusEmbedding.proof h v (HermAtPlace.full h v) (GramAtData.full h v)

theorem le : LineEigenvalue.Statement h v := LineEigenvalue.proof h v (VecAtNeZero.full v)

theorem sh : SemidirectHaar.Statement (archUnitary h v) (InfinitePlace E → ℂˣ) := SemidirectHaar.proof _ _

theorem tm : TorusModulus.Statement h v :=
  TorusModulus.proof h v (HermAtPlace.full h v) (GramAtData.full h v) (ComplementForm.full h)
    (StabilizerLevi.proof h v) (UnipotentModulus.proof h v) (RadicalTorusModulus.proof h v)
    fun _ _ _ _ _ => SemidirectHaar.proof _ _

theorem uh : UnipotentHorizontal.Statement h v :=
  UnipotentHorizontal.proof h v (RationalUnipotent.proof h) (UnipRadicalOfRational.proof h v)
    (ComplementArchCocompact.proof h v)

theorem uz : UnipotentCentral.Statement h v :=
  UnipotentCentral.proof h v (RationalUnipotent.proof h) (UnipRadicalOfRational.proof h v)
    ImaginaryLatticeCocompact.proof

end steps

theorem adelicCovolumeFinite {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : HermitianForm F E W) (v : Basis ι E W) : AdelicCovolumeFinite.Statement h v :=
  AdelicCovolumeFinite.of_remaining (fun _ _ _ _ h _ v => te h v) (fun _ _ _ _ h _ v => le h v)
    (fun _ _ _ _ h _ v => tm h v) (fun _ _ _ _ h _ v => sh h v) (UnitsInvHaar.proof _)
    (fun _ _ _ _ h _ v => UnipotentCoordProper.proof h v) (fun _ _ _ _ h _ v => uh h v)
    (fun _ _ _ _ h _ v => uz h v) h v (te h v) (le h v) (tm h v) (sh h v) (UnipotentCoordProper.proof h v)
    (uh h v) (uz h v)

end CompanionTheory.SWFin
