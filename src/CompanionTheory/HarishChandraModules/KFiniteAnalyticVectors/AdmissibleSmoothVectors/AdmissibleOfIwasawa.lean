module

public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle0002
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle0003
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Transfer
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwasawaDecompositionSecondModel

@[expose] public section

namespace CompanionTheory.D.gk.admitted

theorem admissible_of_iwasawa {n : ℕ} {ε : Fin n → Bool} (h : Iwa ε) : AdmUJ ε :=
  admissible_of_finite_rank finite_rank_of_irreducible_unitary (goodPI_of small_irreducible_representation) transfer_holds exists_averaging_operator h

theorem k_finite_smooth : PI.KFinSmooth :=
  kFinSmooth_of finite_rank_of_irreducible_unitary (goodPI_of small_irreducible_representation) transfer_holds exists_averaging_operator iwasawa_decomposition_second_model garding_finite_smooth_vectors

end CompanionTheory.D.gk.admitted
