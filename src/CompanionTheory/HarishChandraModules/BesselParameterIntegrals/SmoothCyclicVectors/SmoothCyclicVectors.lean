module

public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc

@[expose] public section

namespace CompanionTheory.D.Upq.Sm

theorem smooth_cyclic_vectors : PI.SmoothCyc := smoothCyc_of_kFinSmooth CompanionTheory.D.gk.admitted.k_finite_smooth

end CompanionTheory.D.Upq.Sm
