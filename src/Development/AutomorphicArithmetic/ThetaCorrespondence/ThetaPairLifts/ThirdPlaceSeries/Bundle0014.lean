module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocus
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0005
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0495
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0001
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0600
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0468
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0053
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BcAllStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admBC_of_serLoc : ∀ (D : D7) (P : Pend D), GlobalTheory.TypeLeaf.SerLoc D → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → EigSpan P → CentralElt D → ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∀ π ∈ D.nd.Zgood i, ∃ (Xs : Set (D.nd.X i)) (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i), CutAt i k π Xs β b ∧ TypeLocus P i k Xs := by
  first | exact @_root_.GlobalTheory.CutAtGood.main_alt_alt | exact _root_.GlobalTheory.CutAtGood.main_alt_alt | (intros; apply _root_.GlobalTheory.CutAtGood.main_alt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreMoreStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalPass_of_globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.Pass.GlobalStatement := by
  first | exact @_root_.GlobalTheory.StepGlobalPf.main_alt_alt | exact _root_.GlobalTheory.StepGlobalPf.main_alt_alt | (intros; apply _root_.GlobalTheory.StepGlobalPf.main_alt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointCondH0WallOfCanon
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.HubX
theorem jointCond_H0Wall_of_canon_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → ∀ F : FonOf D.loc D.locA HW, AdmissibleParameterJ.JumpConditions L → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → ∃ M0 h0 : ℕ, GlobalTheory.HubX.JointCond_H0Wall D HW F X M0 h0 := by
  intro _ D L HW R X hX F hJ h41 hFont
  obtain ⟨⟨ep, hJa⟩, hJb, hJc, -, hJe, hJf, -⟩ := hJ
  refine ⟨hOf L, hOf L, ?_⟩
  intro i _ _ hsplit u hu π hπ
  have hnI : ¬ TwistedPlaces.InertK D (D.nd.l i) := by
    intro h2
    unfold TwistedPlaces.SplitK at hsplit
    unfold TwistedPlaces.InertK at h2
    rw [hsplit] at h2
    rcases h2 with h2 | h2 <;> cases h2
  rw [hX.dc i hnI] at hu
  unfold dcOf at hu
  split_ifs at hu with hS
  swap
  · simp [KillingConditions.allRows] at hu
  obtain ⟨_, h5, hq, hd, hg, _⟩ := hS.1
  have hu' : u ∈ placesOver D.host.E (D.nd.l i) := ((Exists.choose hS.2).cover u).1 (Or.inr hu)
  have hl2 : D.nd.l i ≠ 2 := by omega
  have hsm : D.nd.l i ∉ D.host.small := fun h => by
    have h' : primeClass D.host.toHostRaw (D.nd.l i) = PrimeClass.splitK := hsplit
    simp [primeClass, h] at h'
  have hKur := _root_.GlobalTheory.HubLoc.kw_le_Kur_all D i hsm hq hd u hu'
  have hgood : Good (D.nbr i u hu').Kw 1 (D.nbr i u hu').LL :=
    (D.self_good i u hu').good_one (D.nbr i u hu').LL_split hl2 (GlobalTheory.HubLoc.le_Ks_one_of_Kur _ hKur)
  have hZ : π ∈ D.nd.Z i := Formalism.MainNotions.LargeLevelLemmas.zgoodSubsetZ i hπ
  have hfam := hX.fam
  have hdec := (_root_.GlobalTheory.PointConditions.main D X.r X.ρ hfam i π hZ).2.2.2
  have hgr := hfam.good i
  have hcont := hfam.cont i π
  have hWc : Continuous (WpO D.nd i (X.ρ i) π) := by
    have h1 : Continuous fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) := by
      refine ((D.nd.chi_cont i 1).comp continuous_inv).congr fun g => ?_
      simp only [Function.comp_apply]
      rw [MonoidHom.inv_apply, ← map_inv]
    exact h1.smul hcont
  have hLc := GlobalTheory.WordJumpsCompare.continuous_loc D i u hu' _ hWc
  have hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu') ((WpO D.nd i (X.ρ i) π).comp (decS D.nd u))) g v :=
    fun v => hLc.matrix_mulVec continuous_const
  have hJW := fun τ => _root_.GlobalTheory.jumps_WpO_T2O_window D L ep hJa hJb hJc hJe hJf i (X.r i) (X.ρ i) π hgr hZ hdec u hu'
    (TruncatedSeriesCountingIdentities.CoefExt.self i u hu') τ (WpO D.nd i (X.ρ i) π) (Or.inl rfl)
  have hrn : D.R.r ≤ D.R.nV := Nat.le_add_right _ _
  have hnV : 1 ≤ D.R.nV := le_trans D.R.t_odd.pos (Nat.le_add_left _ _)
  have hH := _root_.GlobalTheory.HubX.cH0all_le_of_jumps_at_embeddings D.loc HW D.locA (D.nd.l i) (D.nbr i u hu').Kw (D.nbr i u hu').LL hgood (hOf L) D.R.nV
    (4 * D.R.n) (wLat D i (X.ρ i) π u hu' hc) hKur (GlobalTheory.bridge_finrank_le D i u hu') hnV
    (fun τ => by
      obtain ⟨U, hU1, hU2, hU3⟩ := (hJW τ).1
      exact ⟨U, hU1.trans hrn, hU2, hU3⟩)
  refine ⟨hu', 1, hgood, hc, ?_, hH.1, fun τ => (hJW τ).2, ?_⟩
  · exact (_root_.GlobalTheory.T.decomposition_fontaine_at_places_over_l D i (X.r i) (X.ρ i) π h41 (hFont i) hgr hcont hdec (hg 0) (hg 1) u hu'
      (TruncatedSeriesCountingIdentities.CoefExt.self i u hu')).2.2.1
  · rw [hX.c0]
    exact hH.2
end GlobalTheory.HubX
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointCondH0allCanon
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.HubX
theorem jointCondH0all_canon_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → AdmissibleParameterJ.JumpConditions L → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → ∀ i : D.nd.Loc, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, ∃ M0 h0 : ℕ, GlobalTheory.HubX.DecompositionInvariantsCondition D HW i (X.ρ i) π (X.dc i) (X.c0 i) M0 h0 := by
  intro hF D L HW R X hC hJ h41 hAdm i hTw hg hRA hS π hπ
  obtain ⟨⟨ep, hep⟩, hJb, hJc, hJd, hJe, hJf, hJg⟩ := hJ
  have hls : D.nd.l i ∉ D.host.small := fun h => hRA.1 (Or.inl h)
  have hl2 : D.nd.l i ≠ 2 := UpperTheory.Small.ne_two D.host hls
  have hlq : D.nd.l i ≠ D.host.q := fun h => hRA.2.1 (Or.inl h)
  have hld : D.nd.l i ≠ D.host.d := fun h => hRA.2.1 (Or.inr h)
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hπZ : π ∈ D.nd.Z i := LargeLevelLemmas.zgoodSubsetZ i hπ
  obtain ⟨-, -, -, hdec⟩ := _root_.GlobalTheory.PointConditions.main D X.r X.ρ hC.fam i π hπZ
  have hgood := hC.fam.good i
  have hcont := hC.fam.cont i π
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    unfold Ranks.r
    omega
  have hrV : D.R.r ≤ D.R.nV := Nat.le_add_right _ _
  refine ⟨hOf L, hOf L, hl2, ?_⟩
  intro u _ w hw _
  have hur : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) := _root_.GlobalTheory.HubLoc.kw_le_Kur_all D i hls hlq hld w hw
  refine ⟨GlobalTheory.HubLoc.le_Ks_one_of_Kur _ hur, ?_⟩
  intro C hs hc L2
  have hcrys := (_root_.GlobalTheory.T.decomposition_fontaine_at_places_over_l D i (X.r i) (X.ρ i) π h41 (hAdm i) hgood hcont hdec hg0 hg1 w hw C).2.2.2
  have hjump := fun τ => _root_.GlobalTheory.jumps_WpO_T2O_window D L ep hep hJb hJc hJe hJf i (X.r i) (X.ρ i) π hgood hπZ hdec w hw C τ
    (T2O D.nd i (X.ρ i) π) (Or.inr rfl)
  have key := _root_.GlobalTheory.HubX.cH0all_le_of_jumps_at_embeddings D.loc HW D.locA (D.nd.l i) (D.nbr i w hw).Kw C.LL hs (hOf L) D.R.r (4 * D.R.n)
    (tTwoLocalLattice D i (X.ρ i) π C hc L2) hur (GlobalTheory.bridge_finrank_le D i w hw) hr1 (fun τ => (hjump τ).1)
  refine ⟨hcrys, key.1, fun τ => (hjump τ).2, ?_⟩
  rw [hC.c0]
  refine key.2.trans ?_
  unfold c0of
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hrV)) _
end GlobalTheory.HubX
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltMoreStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaine_quotient_degrees_of_ptFam : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D), _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D → AdmissibleParameterJ.ConclusionJa D → ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ := by
  first | exact @_root_.GlobalTheory.HubFon.main_alt_alt | exact _root_.GlobalTheory.HubFon.main_alt_alt | (intros; apply _root_.GlobalTheory.HubFon.main_alt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltTerStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimpleDecomposition_of_goodR : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D), _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D → AdmissibleParameterJ.ConclusionJa D → AdmissibleParameterJ.jcCondition L → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π := by
  first | exact @_root_.GlobalTheory.GTwoTheta.main_alt_alt | exact _root_.GlobalTheory.GTwoTheta.main_alt_alt | (intros; apply _root_.GlobalTheory.GTwoTheta.main_alt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admDict_of_weight_blockChar : GlobalTheory.TwSys.Cheb → ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → WeightParam D → BlockCharParam D → AdmissibleParameterJ.AdmDict D := by
  first | exact @_root_.GlobalTheory.BridgeAdmDict.main_alt_alt | exact _root_.GlobalTheory.BridgeAdmDict.main_alt_alt | (intros; apply _root_.GlobalTheory.BridgeAdmDict.main_alt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemZAndCuspOfStepsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prvG6_of_admissible_of_g6_decomposition : _root_.GlobalTheory.StringRepresentationDecomposition.CentredStringDecompositionAlt → _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight' → _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation' → _root_.GlobalTheory.StringRepresentationDecomposition.MuCharacterCondition → EigenCharTwist → _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount → Numerics → Rest → ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → SumRepresentations.ConclusionG6 D := by
  first | exact @_root_.GlobalTheory.EigenPoint.prvG6_of_realisation_mu_res_count_numerics | exact _root_.GlobalTheory.EigenPoint.prvG6_of_realisation_mu_res_count_numerics | (intros; apply _root_.GlobalTheory.EigenPoint.prvG6_of_realisation_mu_res_count_numerics <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MuBlockMemStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_mu_piece_mem_base_change : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm3 D → SumRepresentations.adm5 D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → GlobalTheory.RowCopy.RowSize D → GlobalTheory.RowCopy.HeckeSplitOne D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → thetaOf D.nd D.naut i σ P → IsBCV D.nd D.naut i P Pa → (⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa := by
  first | exact @_root_.GlobalTheory.MuBlock.mu_block_mem_alt | exact _root_.GlobalTheory.MuBlock.mu_block_mem_alt | (intros; apply _root_.GlobalTheory.MuBlock.mu_block_mem_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OChooseStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_chosen_of_cheb_oSplit : GlobalTheory.TwSys.Cheb → ∀ (D : D7), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc, ZDecomp D.nd i → Live D.nd i → ∃ S : Finset ℂ, Chosen D.nd D.naut i ↑S := by
  first | exact @_root_.GlobalTheory.OChoose.oChoose_alt | exact _root_.GlobalTheory.OChoose.oChoose_alt | (intros; apply _root_.GlobalTheory.OChoose.oChoose_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointInputAwayFromTypePrimes
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory
theorem pointInputAwayFromTypePrimes_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (X : KillingConditions.HubData D), GlobalTheory.PtCore.PtFam D X.r X.ρ → _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D → ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, GlobalTheory.HTW.RecS.PtIn i (X.r i) (X.ρ i) π := by
  intro hF D X hX hG i hl π hπ
  have hZ := LargeLevelLemmas.zgoodSubsetZ i hπ
  have hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i (X.r i) (X.ρ i) π := by
    obtain ⟨e, he⟩ := (hX.compl i π hZ).rho
    exact ⟨e, fun g u => he g u⟩
  have h0 : D.nd.l i ≠ D.host.g 0 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have h1 : D.nd.l i ≠ D.host.g 1 := fun h => hl (by simp [TwistedPlaces.gset, h])
  exact ⟨hX.good i, fun x => (hX.good i x).1, hZ, hd, hX.cont i π, fun w hw C x =>
    ((_root_.GlobalTheory.T.semisimple_decomposition_of_good_galois_local hF D i _ _ π (hX.good i) (hG i _ (hX.good i)) h0 h1 hd w hw C).2 x).2⟩
end GlobalTheory
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestPtOfPtFam
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
end
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo
end GlobalTheory.CrysFromGTwo
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.DualTwistCrys
end GlobalTheory.DualTwistCrys
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.CrysChiOne
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}
end GlobalTheory.CrysChiOne
end
section
namespace Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open NumberField IsDedekindDomain
end Formalism.MainNotions.N
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open GlobalTheory.RestPtAssembly in
theorem GlobalTheory.restPt_of_ptFam_aux41_oSplit : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, RestPt i (r i) (ρ i) π := by
  intro hF D r ρ hP h41 hO i hl π hπ
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have hZ : π ∈ D.nd.Z i := by
    have hx := hπ
    rw [D.Z_tie]
    rw [D.Zgood_tie] at hx
    exact hx.1
  obtain ⟨hrho, hss, hblock, hdec⟩ := _root_.GlobalTheory.PointConditions.main D r ρ hP i π hZ
  obtain ⟨hshape, heps⟩ := GlobalTheory.T.admissible_shape_and_epsilon_at_every_localisation D i
  have hG2 := ((h41 i).2.2 _ (hP.good i)).2.1
  have hX := _root_.GlobalTheory.T.semisimple_decomposition_of_good_galois_local hF D i (r i) (ρ i) π (hP.good i) hG2 hg0 hg1 hdec
  exact
    { ng0 := hg0
      ng1 := hg1
      good := hP.good i
      chi1 := fun w hw C => (hX w hw C).1
      block := hblock
      chi := fun w hw C c h1 h2 => chiRat_isCrys D i w hw C c h1 h2
      g3 := UpperTheory.GalS.jointCondition_of_constituentCondition_split D i _ (hP.good i) ((_root_.UpperTheory.GalS.g3' ((h41 i).2.2 _ (hP.good i)).2.2.1).1 (Or.inl ⟨hg0, hg1⟩)) (hO i)
      cont := hP.cont i π
      rho := hrho
      ss := hss
      eps := heps
      shape := hshape }
end
end
end
end

