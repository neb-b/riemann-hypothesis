module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.CoefEig
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa

@[expose] public section

namespace CompanionTheory.CapEig

theorem coefEig_of_infChar (hI : PI.DSInfCharCap.DSInfCharCap) : CompanionTheory.LimBd.Main.CoefEig :=
  coefEig_of hI CompanionTheory.D.gk.admitted.k_finite_smooth

end CompanionTheory.CapEig
