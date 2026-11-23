module

public import Development.EtaleCohomology.TateTwists.Bundle0030
public import Development.EtaleCohomology.TateTwists.Bundle0033
public import Development.EtaleCohomology.TateTwists.StepPf
public import Development.EtaleCohomology.TateTwists.Bundle0032
public import Development.EtaleCohomology.TateTwists.Bundle0024
public import Development.EtaleCohomology.TateTwists.conePf
public import Development.EtaleCohomology.TateTwists.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.EtaleCohomology.TateTwists.Bundle0007
public import Development.EtaleCohomology.TateTwists.Bundle0031
public import Development.EtaleCohomology.TateTwists.MuTwistQuotientEmbedsInUnitTorsorPresheaf
public import Development.EtaleCohomology.TateTwists.Bundle0027
public import Development.EtaleCohomology.TateTwists.Bundle0016

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.EtaleComplexAcyclicIffLocalExactness
section
namespace LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso
theorem etale_complex_acyclic_iff_local_exactness : LateralTheory.EtaleFoundations.acyc.acycIff := by
  apply LateralTheory.EtaleFoundations.acyc.acycIff_of
theorem etale_tensor_column_acyclic_of_flat : LateralTheory.EtaleFoundations.acyc.column := by
  apply LateralTheory.EtaleFoundations.acyc.column_of
theorem etale_tensor_staircase_lifting_inductive : LateralTheory.EtaleFoundations.stairPf.Step := by
  apply LateralTheory.EtaleFoundations.StepPf.Step_of
theorem etale_tensor_acyclic_of_staircase_lifting : LateralTheory.EtaleFoundations.acyc.stair := by
  apply LateralTheory.EtaleFoundations.acyc.stair_of <;> first | exact etale_tensor_staircase_lifting_inductive
theorem etale_tensor_acyclic_cone_of_flat : LateralTheory.EtaleFoundations.tqis.acyc := by
  apply LateralTheory.EtaleFoundations.tqis.acyc_of <;> first | exact etale_complex_acyclic_iff_local_exactness | exact etale_tensor_column_acyclic_of_flat | exact etale_tensor_acyclic_of_staircase_lifting
theorem etale_tensor_mappingCone_commutes : LateralTheory.EtaleFoundations.tqis.cone := by
  apply LateralTheory.EtaleFoundations.tqis.cone_of
theorem etale_tensor_quasiIso_of_acyclic_cone : LateralTheory.EtaleFoundations.EtaleTensorPairQuasiIsoOfFlatQuasiIso := by
  apply LateralTheory.EtaleFoundations.etale_tensor_preserves_quasiIso_of_acyclic_and_cone <;> first | exact etale_tensor_acyclic_cone_of_flat | exact etale_tensor_mappingCone_commutes
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTensorPairQuasiIsoOfFlatQuasiIso := etale_tensor_quasiIso_of_acyclic_cone
end LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizSuccHolds
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_cup_alexanderWhitney_leibniz_succ_holds : EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree := by
  intro R _ I J K μ E n m k n₁ m₁ k₁ hk hn hm hk₁ hk₂ α β γ γ₁ γ₂ ha h1 h2 P w h U x
  subst hn hm
  obtain rfl : k₁ = k + 1 := by omega
  have e := LateralTheory.EtaleFoundations.etaleAlexanderWhitneyCup_leibniz_of_pairing R μ hk α β γ γ₁ γ₂ ha h1 h2
  rw [e, ev_add', awleib_ev_smul]

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleKummerTorsorRootsOfUnityListTorsionExistsOf
section
namespace LateralTheory.Fin.EtaleKummerTriangleExists
theorem etale_kummer_torsor_roots_of_unity_list_torsion_exists_of_components : LateralTheory.EtaleFoundations.MuRootListProductOneSumEtaleLocallyZero := by
  apply LateralTheory.EtaleFoundations.mu_root_list_product_one_sum_etale_locally_zero
theorem etale_kummer_torsor_roots_of_unity_torsion_exists_of_components : LateralTheory.EtaleFoundations.ExistsEtaleMonoMuTwistKillingRootRelations := by
  apply LateralTheory.EtaleFoundations.exists_etale_mono_mu_twist_quotient_of_root_lists_locally_zero <;> first | exact etale_kummer_torsor_roots_of_unity_list_torsion_exists_of_components
theorem etale_kummer_torsor_torsion_preimage_exists_of_components : LateralTheory.EtaleFoundations.MuTwistQuotientEmbedsInUnitTorsorPresheaf := by
  apply LateralTheory.EtaleFoundations.mu_twist_quotient_embeds_in_unit_torsor_presheaf
theorem etale_kummer_torsor_torsion_exists_of_components : LateralTheory.EtaleFoundations.EtaleKummerSectionsIntoTwistEmbeddingExist := by
  apply LateralTheory.EtaleFoundations.exists_etale_mono_mu_twist_into_torsor_sheaf_of_presheaf <;> first | exact etale_kummer_torsor_roots_of_unity_torsion_exists_of_components | exact etale_kummer_torsor_torsion_preimage_exists_of_components
theorem etale_kummer_torsor_extension_exists_of_components : LateralTheory.EtaleFoundations.EtaleTwistExtendsThroughMonoToResolutionZero := by
  apply LateralTheory.EtaleFoundations.etale_twist_extends_through_mono_to_resolution_holds
theorem etale_kummer_torsor_exists_of_components : LateralTheory.EtaleFoundations.EtaleKummerTriangleExists := by
  apply LateralTheory.EtaleFoundations.etale_kummer_torsor_class_exists_of_tors_and_ext <;> first | exact etale_kummer_torsor_torsion_exists_of_components | exact etale_kummer_torsor_extension_exists_of_components
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleKummerTriangleExists := etale_kummer_torsor_exists_of_components
end LateralTheory.Fin.EtaleKummerTriangleExists
end

