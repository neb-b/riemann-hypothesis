module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0008
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0065

@[expose] public section

theorem UpperTheory.Reformulated.B.InfiniteNormOneField.infinite_norm_one_k {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {nS nT : ℕ}
    {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
    {θ : NumberField.InfinitePlace F → TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) E →+* ℂ}
    {ι : (NumberField.InfinitePlace F → ℂ) →+ Formalism.IndefR.DatumF.AEF F E}
    (h : PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) : {t | t * σ t = 1}.Infinite :=
  have hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ := h.1.cm
  UpperTheory.Reformulated.B.CapelliAbsoluteValue.abs σ hcm.2.1 hcm.2.2.2
