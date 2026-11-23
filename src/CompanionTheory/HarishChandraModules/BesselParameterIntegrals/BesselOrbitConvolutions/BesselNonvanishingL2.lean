module

public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.DoubleCosetDecomposition
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.Bundle0002
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.NormId
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0042
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0046
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.VanishingOfL2Equivariant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.QuadAOf
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.QuadBOf
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingFromL2
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0155

@[expose] public section

namespace CompanionTheory.D.Upq.BesselFunctionalConstruction

open Formalism.FourierDecayAlt.P

theorem decDD : DecDD := G.double_coset_decomposition
theorem beConv : BeConv := G.bessel_integral_convergence_of_growth growth_spherical_bound
theorem beBessel : BeBessel := PI.WBL.S5.G.beBessel_of growth_spherical_bound
theorem normIdSm : NormIdSm :=
  PI.WBL.NIS.G.normIdSm_of growth_spherical_bound growth_group_bound PI.WBL.NIS.measSideP
theorem kFinForm : KFinForm := kFinForm_of beConv beBessel
theorem zeroCase : ZeroCase := UnipotentHaarMeasurability.G.zeroCase_of beConv normIdSm schur_hermitian
theorem zeroCaseDD : ZeroCaseDD := UnipotentHaarMeasurability.G.zeroCaseDD_of beConv normIdSm schur_hermitian
theorem ooConv : OOConv :=
  S3dx4.G.ooConv_of schur_hermitian normIdSm norm_inverse_bound growth_group_bound decDD beConv
theorem quadConv : QuadConv := by
  intro hIn k r Wp Wq _ _ _ _ _ _ _ _ D ε lam h H _ _ _ σ w0 u u' νq νq' hS1 hS2 l l' hbe hbe'
  exact ⟨fun γ hγ => S3dx4.G.quadA_of schur_hermitian normIdSm norm_inverse_bound growth_group_bound
      decDD beConv hIn D hS1 hS2 hbe hbe' hγ,
    S3dx4.G.quadB_of norm_inverse_bound growth_spherical_bound growth_group_bound decDD hIn D hS1 hbe⟩
theorem bessel_nonvanishing_L2 : BesselNonvanishingL2 :=
  MatrixMultiplicationContinuity.G.bessel_nonvanishing_from_L2 schur_hermitian norm_inverse_bound growth_spherical_bound
    growth_group_bound decDD beConv

end CompanionTheory.D.Upq.BesselFunctionalConstruction
