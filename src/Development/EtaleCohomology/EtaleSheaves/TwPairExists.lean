module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0003
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0011
public import Development.EtaleCohomology.TateTwists.Bundle0013
public import Development.EtaleCohomology.TateTwists.Bundle0025
public import Development.EtaleCohomology.TateTwists.Bundle0031
public import Development.EtaleCohomology.TateTwists.Bundle0017
public import Development.EtaleCohomology.TateTwists.Bundle0022
public import Development.EtaleCohomology.TateTwists.Bundle0029
public import Development.EtaleCohomology.TateTwists.Bundle0026
public import Development.EtaleCohomology.TateTwists.Bundle0012
public import Development.EtaleCohomology.TateTwists.Bundle0023
public import Development.EtaleCohomology.TateTwists.Bundle0032
public import Development.EtaleCohomology.TateTwists.Bundle0030
public import Development.EtaleCohomology.TateTwists.Bundle0018
public import Development.EtaleCohomology.TateTwists.Bundle0019
public import Development.EtaleCohomology.TateTwists.Bundle0016
public import Development.EtaleCohomology.TateTwists.Bundle0015
public import Development.EtaleCohomology.TateTwists.Bundle0034
public import Development.EtaleCohomology.TateTwists.Bundle0035
public import Development.EtaleCohomology.TateTwists.Bundle0027
public import Development.EtaleCohomology.TateTwists.Bundle0010
public import Development.EtaleCohomology.TateTwists.Bundle0007
public import Development.EtaleCohomology.TateTwists.Bundle0011
public import Development.EtaleCohomology.TateTwists.Bundle0024
public import Development.EtaleCohomology.TateTwists.Bundle0033

@[expose] public section

namespace LateralTheory.Fix.CupProductTensor
open LateralTheory.EtaleFoundations

theorem cup_spec0 : t_cup_spec0 := LateralTheory.Fin.EtaleCupProductNaturalInCoefficients.etale_cup_product_compatibility_specification_of_components
theorem cup_assoc0 : EtaleCochainCupAssociativeOfPairing :=
  etale_cochain_cup_assoc_of_cup_spec_and_alexander_whitney_assoc cup_spec0 (t_aw_assoc0_of etale_chain_cochain_eval_basic_properties_hold simplicial_subinterval_of_subinterval_along_etale)
theorem secSep : EtaleTensorTripleProductLeibnizSeparated.SecSep := etale_sheaf_sections_separated_holds
theorem tens_tri : EtaleTensorPairProductAssociative :=
  etale_tensor_triple_product_of_family_and_leibniz (etale_tensor_triple_product_family_of_gluing LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue.intersectionNumber_baseChange)
    (etale_tensor_triple_product_leibniz_of_separated secSep)
theorem tens_ex : tt_tens_ex := tt_tens_ex_of tt_tens_pre_of etale_presheaf_tensor_data_sheafification_is_tensor_complex
theorem univ_exdeg : twpair_tens_univ_exdeg := twpair_tens_univ_exdeg_of
theorem tens_univ : twpair_tens_univ := twpair_tens_univ_of univ_exdeg
theorem tens_ge : tt_tens_ge := tt_tens_ge_of (by intro R _ I J K τ hτ; exact (tens_univ R τ hτ).2.1)
theorem res_side : tt_res_side := tt_res_side_of tens_univ LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso.intersectionNumber_baseChange
theorem twres_ext : EtaleTwistResolutionUniversalExtension := LateralTheory.Fin.EtaleTwistResolutionUniversalExtension.intersectionNumber_baseChange
theorem cup_compat : EtaleCupProductNaturalInCoefficients := LateralTheory.Fin.EtaleCupProductNaturalInCoefficients.intersectionNumber_baseChange

theorem holds_of (hts : EtaleTateTwistSectionsLocallyGenerated) :
    EtaleTwistedCupProductAssociative ∧ EtaleTwistResolutionPairingCupUnique := by
  have hsec : TwMulGenMap.twSec := hts
  have hloc : EtaleTateTwistSectionsLocallyMultiplesOfGenerator := fun q _ i => (hts q i).1
  have hinj : EtaleTateTwistGeneratorMapSectionsInjective := etale_tate_twist_generator_map_injective_of_sections_glue hts LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange
    LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue.intersectionNumber_baseChange
  have tw_mul : EtaleTateTwistSingletonTensorGenMul := etale_tate_twist_tensor_iso_of_generator_map_iso (etale_tate_twist_multiplication_tensor_exists_of_complex_tensor_exists tens_ex) (etale_tate_twist_multiplication_generator_map_of_section_description hsec)
    (etale_tate_twist_generator_map_isIso_of_inj_surj etale_sheaf_mono_epi_iff_sections_of_separation (etale_tate_twist_generator_map_surjective_of_local_and_root hloc
      etale_tate_twist_generator_restriction_and_root_change_holds) hinj)
  have twist : tt_twist_side := tt_twist_side_of tw_mul LateralTheory.Fin.EtaleTateTwistSheafFlat.intersectionNumber_baseChange LateralTheory.Fin.EtaleComplexPairingFlipExists.intersectionNumber_baseChange
    LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso.intersectionNumber_baseChange
  have twres : EtaleTensorPairTwistResolutionMul := etale_tensor_twisted_resolution_of_existence_bound_and_sides tens_ex tens_ge twist res_side
  have pa : t_pair_assoc := t_pair_assoc_of twres tens_tri twres_ext cup_compat cup_assoc0 t_pa_tens_ex_of
    t_pa_tens_univ_of t_pa_precomp_of t_pa_cpush_id_of t_pa_cpush_htpy_of
  have tp : EtaleTwistResolutionPairingCupUnique := etale_tate_twist_cup_pairing_of_tensor_and_resolution_properties tens_ex tens_univ twres twres_ext cup_compat twpair_zc_fun_of
  exact ⟨etale_twisted_cup_assoc_of_twisted_pairing_exists_assoc (t_twpair_ex_of tp) pa, tp⟩

theorem ringAssoc : LateralTheory.E.CupProductRingLaws.LeafRingAssoc := (holds_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec).1
theorem cupSpec : LateralTheory.E.CupProductRingLaws.LeafCupSpec := fun R _ _ _ _ μ E _ _ _ hk => cup_spec0 R μ (E := E) hk
theorem ringComm (hf : cc_cup_flip) : LateralTheory.E.CupProductRingLaws.LeafRingComm :=
  etale_twisted_cup_graded_comm_of_flip_and_unique_pairing hf (fun R _ _ _ _ μ => (LateralTheory.Fin.EtaleComplexPairingFlipExists.intersectionNumber_baseChange R μ).imp fun _ h => h.1) (holds_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec).2
theorem awFlip : cc_aw_flip := cc_aw_flip_of LateralTheory.Fin.PrismAlexanderWhitneySwapChainHomotopy.intersectionNumber_baseChange cupflip_eta_delta_of

theorem cupFlip : cc_cup_flip := by
  intro R _ I J K μ ν hf E n m k h h' a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (cupSpec R μ E h).1 α β
  obtain ⟨γ', hγ'⟩ := (cupSpec R ν E h').1 β α
  rw [(cupSpec R μ E h).2 _ _ _ hγ, (cupSpec R ν E h').2 _ _ _ hγ']
  exact awFlip R μ ν hf E h h' α β γ γ' hγ hγ'
theorem ringComm' : LateralTheory.E.CupProductRingLaws.LeafRingComm := ringComm cupFlip
theorem twPairExists : LateralTheory.E.CupProductRingLaws.LeafTwPairExists := fun q _ i j => ⟨_, ((holds_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec).2 q i j).1⟩
end LateralTheory.Fix.CupProductTensor
