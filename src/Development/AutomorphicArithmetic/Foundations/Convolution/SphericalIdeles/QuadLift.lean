module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.QuadLiftOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.CoreId
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.VarTrace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemPairJHolds

@[expose] public section

theorem UpperTheory.ConvolutionTheory.Sph.ramSph : UpperTheory.ConvolutionTheory.Sph.RamSph :=
  UpperTheory.ConvolutionTheory.Sph.ramSphOf UpperTheory.Gal.Join.locGal (UpperTheory.Gal.Join.liftGood
    (UpperTheory.Gal.Join.coreId UpperTheory.Gal.InertialTypesAlt.G.varEx UpperTheory.Gal.InertialTypesAlt.G.varTrace UpperTheory.Gal.InertialTypesAlt.L.elemPairJ_holds))

theorem UpperTheory.ConvolutionTheory.Sph.quadLift : GlobalTheory.GalCut.QuadLift := UpperTheory.ConvolutionTheory.Sph.quadLiftOf UpperTheory.ConvolutionTheory.Sph.ramSph
