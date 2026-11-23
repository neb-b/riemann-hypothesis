module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CuspOfCq
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeE
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.RankOneOfLong
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AllCuspidalOpenBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GoodRCongr
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsLast
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.GoodDepthZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
theorem main_alt_alt : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D →
    (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) → Formalism.MainNotions.N.GlobalDatumDepthZeroCondition D := by
  intro D hT hA h41 _ a x hx Sig hSig k v
  obtain ⟨-, Sig', hSig', hgood⟩ := hx
  have hc : ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b := hA.2.2
  have hL := charSum_of_tie D hT.1 hc
  obtain ⟨P, hP, hB⟩ := hSig
  obtain ⟨P', hP', hB'⟩ := id hSig'
  have hperm := ((h41 a).2.1 P P' (by rw [hP]; simp) (hP.trans hP'.symm)).1 _ _ hB hB'
  have e1 := GlobalTheory.RowTie.isoLoc_perm D.nd D.naut hperm (D.naut.plGw k v)
  rw [GlobalTheory.LocCongrRoad.isoLoc_twist _ _ hL, GlobalTheory.LocCongrRoad.isoLoc_twist _ _ hL] at e1
  have e2 := congrArg (fun b => D.naut.lpChar b (D.naut.locG D.naut.etaT (D.naut.plGw k v))) e1
  simp only [lpChar_eta_back D hT.1] at e2
  rw [GlobalTheory.LocCongrRoad.isoLoc_append_singleton, GlobalTheory.LocCongrRoad.isoLoc_append_singleton] at e2
  rw [hc _ _ _ _ e2]
  exact GlobalTheory.PointIrredCompare.fullLabels_of_good D.nd D.naut hSig' hgood k v
end GlobalTheory.GoodDepthZero
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibility
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.PairedCharacterCondition
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Module Polynomial
variable {D : D7}
def PairedCharacterConditionAlt (C : ℝ) (CT : ℕ) : Prop :=
  ∀ (i : D.nd.Loc) (k k' : Fin 2), k ≠ k' → D.nd.l i = D.host.g k →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))),
    GoodR D.nd i r → (∀ π ∈ D.nd.Z i, Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) →
  ∀ (eta s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool)
    (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ),
    eta + D.R.t + 1 < s →
    Real.log (D.host.g k' : ℝ) ≤ 2 * Real.log (D.host.g k : ℝ) →
    CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k →
    SignOK i sg → HostJ i r eta s S sg U → (∀ π ∈ D.nd.Zgood i, Br.sFin D.loc D.nbr i ρ π) →
    (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
    (D.nd.etaLoc i : ℝ) ≤ ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ) * rhs C eta i ρ π
def GaloisFamilyConditions' : Prop :=
  ∀ i r, GoodR D.nd i r →
    Formalism.MainNotions.SumRepresentations.At.G1 D.nd i r ∧ _root_.UpperTheory.GalS.G2a D.nd D.naut i r ∧ _root_.UpperTheory.GalS.G3 D.nd i r ∧
      Formalism.MainNotions.SumRepresentations.At.G4 D.nd i r
def LocalGlobalCompatibility' : Prop := _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D
section Pending
end Pending
end Formalism.MainNotions.PairedCharacterCondition
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAltBis
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
namespace GlobalTheory.AlgCharFromGal
theorem main_alt_alt_alt : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → GlobalTheory.JumpDictionaryFoundation.AlgebraicCharacter_at D := by
  intro D hA i π s z hz
  obtain ⟨ρ, hc, h1, h2⟩ := (_root_.UpperTheory.GalS.weak' hA i).2.2 π s (fun τ x hx => ⟨z τ, by
      have := Multiset.mem_map_of_mem (fun y => y + (s : ℂ)) hx
      rwa [hz τ, Multiset.mem_singleton] at this⟩)
  refine ⟨ρ, hc, fun w hw hu B σ hB hσ => ?_, fun w hw => (h2 w hw).1, fun τ => ?_⟩
  · have hu' : D.naut.unr (D.naut.wdOf i ρ w) := by
      rw [h1 w hw]; exact (D.naut.unr_tw _ _).2 hu
    have e := D.naut.wdOf_frob i ρ w hw hc hu' B σ hB hσ
    have hcard : Multiset.card (D.naut.frobEig (D.naut.wdOf i ρ w)) = 1 := by
      rw [D.naut.frobEig_card _ hu', D.naut.wdOf_dim]
    obtain ⟨α, hα⟩ := Multiset.card_eq_one.1 hcard
    rw [hα, Multiset.map_singleton, Multiset.prod_singleton, charpoly_fin_one, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C] at e
    rw [← h1 w hw, hα]
    congr 1
    have e0 := congrArg (fun p => p.coeff 0) e
    simpa using e0.symm
  · obtain ⟨w, hw, hτ⟩ := GlobalTheory.GaloisInputCompare.exists_inducesW D.nd i τ
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [(h2 w hw).2.2 τ hτ]
    have e := hz ((D.naut.iotaQC i).toRingHom.comp τ)
    rw [show (fun y : ℂ => -(y + (s : ℂ))) = (fun y => -y) ∘ (fun y => y + (s : ℂ)) from rfl,
      ← Multiset.map_map, e]
    simp
end GlobalTheory.AlgCharFromGal
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAltMore
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.ChiOneNoPt
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary GlobalTheory.JumpDictionaryFoundation
theorem main_alt_alt_alt : GlobalTheory.Published.FontaineBcris → ∀ D : D7, SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D →
    GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D → GlobalTheory.HubX.MuUnr D → ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D →
    GlobalTheory.PtCore.ChiOneE D i := by
  intro hF D _h0 h2 h5 hB hM i hl w hw L' hL
  obtain ⟨ρ, hρc, haway, habove⟩ :=
    (_root_.UpperTheory.GalS.weak' h2 i).2.2 (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (sOne D) (integral D hB i)
  have hρ := eq_chi D h5 i w hw ρ hρc haway
  obtain ⟨hdR, hwd, -⟩ := habove w hw
  have hun : D.naut.unr (D.naut.wdOf i ρ w) := by
    rw [hwd]; exact (D.naut.unr_tw _ _).2 (hM i hl w hw)
  have hcW : D.naut.IsCrysW i ρ w := (D.naut.wdOf_unrL i ρ w hw hρc hdR).1 hun
  subst hρ
  have hc : Br.IsCrysW D.loc D.nbr i w hw (chiGL D i 1) :=
    (((D.loc_tie i w hw).2.1 1 _ (continuous_chiGL D i 1)).1).1 hcW
  have hR := GlobalTheory.BlockCrys.subDualRules_of_fontaine hF (D.nd.l i) (D.loc _) (D.locA _) ⟨D.locT _⟩
  have hE := GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc _) (D.nbr i w hw).Kw (D.nbr i w hw).LL L' hL _ _
    ((GlobalTheory.BlockCrys.matCrysAt_iff D i w hw _).2 hc)
  exact GlobalTheory.BlockCrys.isCrys_inv _ (hR.1 _ _) (hR.2 _ _) _
    (GlobalTheory.ChiOneEnl.isCrys_chiE_of_constituent D i w hw L' hL (hR.1 _ _) _ _ (isConstituent_chiGL D i) hE)
end GlobalTheory.ChiOneNoPt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAltTer
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
noncomputable section
namespace GlobalTheory.GaloisFromAdm
theorem main_alt_alt_alt : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → GlobalTheory.BlockComplement.GaloisRepsCusp D := by
  intro D h i a ha π hc hr
  obtain ⟨ρ, hcont, hss, haway, -⟩ := (_root_.UpperTheory.GalS.weak' h i).1 a ha π hc hr
  refine ⟨ρ, hcont, hss, ?_⟩
  have hfin := placesOver_finite D (D.nd.l i) (Fact.out : (D.nd.l i).Prime).ne_zero
  filter_upwards [D.naut.locG_unr_ae π, hfin.eventually_cofinite_notMem] with w hu hw B φ hB hφ
  rw [D.naut.wdOf_frob i ρ w hw hcont (by rw [(haway w hw).eq_of_unr ((D.naut.unr_tw _ _).2 hu)]; exact (D.naut.unr_tw _ _).2 hu) B φ hB hφ,
    (haway w hw).eq_of_unr ((D.naut.unr_tw _ _).2 hu)]
  rfl
end GlobalTheory.GaloisFromAdm
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTyzAlt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
noncomputable section
namespace GlobalTheory.BCPerm
abbrev _root_.GlobalTheory.BCPerm.mainTheorem : Prop :=  ∀ D : D7, SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i)
    (P0 PI : D.naut.AV i) (Pa0 Pa : List (Part D.naut.CG)), D.naut.ptV i P0 = some x →
    D.naut.ptV i PI = some x → IsBCV D.nd D.naut i P0 Pa0 → IsBCV D.nd D.naut i PI Pa → Pa0.Perm Pa
end GlobalTheory.BCPerm
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartFrobEigNormO
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.PartUnitary
theorem frobEig_openB_and_norm_one_of_isBCV : ∀ (D : D7), SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → ∀ (i : D.nd.Loc) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), IsBCV D.nd D.naut i P Pa → ∀ p ∈ Pa, ∀ w : PlE D.host,
    D.naut.unr (D.naut.locG p.π w) → ∀ α ∈ D.naut.frobEig (D.naut.locG p.π w), UpperTheory.GalN.OpenB (Formalism.ConjugateSelfDual.normV w) α ∧ (p.a = 1 → ‖α‖ = 1) := by
  intro D ht hT i P Pa hB p hp w hu α hα
  have hW := GlobalTheory.LocalInv.weightRegular_of_ext D.nd D.naut D.nbc
  have hAut := ht.2.1
  obtain ⟨ha1, hd1, hcsd⟩ := hB.1 p hp
  have hle : ∀ τ, (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤
      D.naut.infWt i τ := by
    intro τ
    rw [← hB.2.2.2.2.2 τ]
    unfold isoInf
    refine le_trans ?_ (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))
    refine List.single_le_sum (fun _ _ => Multiset.zero_le _) _
      (List.mem_map_of_mem (f := fun k : ℂ => (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - k))) ?_)
    rw [GlobalTheory.LocalInv.list_coe]
    exact List.mem_map_of_mem (List.mem_range.mpr hd1)
  have hnd : ∀ τ, (D.naut.infG p.π τ).Nodup := fun τ =>
    Multiset.Nodup.of_map _ (Multiset.nodup_of_le (hle τ) (hW i P τ).1)
  have hint : ∀ τ, ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ,
      z + ((p.d : ℂ) - 1) / 2 = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
    intro τ z hz
    obtain ⟨k, hk⟩ := (hW i P τ).2 _ (Multiset.mem_of_le (hle τ) (Multiset.mem_map_of_mem _ hz))
    exact ⟨k, by rw [← hk]; push_cast; ring⟩
  rcases Int.even_or_odd ((D.R.nV : ℤ) - p.d - p.a + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hr : D.naut.ralg p.π := (D.naut.ralg_def _).2 fun τ => ⟨hnd τ, fun z hz => by
      obtain ⟨k, hk⟩ := hint τ z hz
      refine ⟨k + m, ?_⟩
      have hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = (m : ℂ) + m := by
        exact_mod_cast hm
      push_cast at hm' ⊢
      linear_combination hk + (1 / 2 : ℂ) * hm'⟩
    exact (_root_.UpperTheory.GalN.tempo' hT p.a p.π ha1 hcsd hr w).part hu α hα
  · have hr : D.naut.ralg (D.naut.tw p.π D.naut.etaT) := (D.naut.ralg_def _).2 fun τ => by
      obtain ⟨s, hs, k0, hk0⟩ : ∃ s : ℂ, D.naut.infG D.naut.etaT τ = {s} ∧ ∃ k0 : ℤ, s = (k0 : ℂ) + 1 / 2 := by
        rcases (hAut.2.1 τ).1 with h | h
        · exact ⟨1 / 2, h, 0, by simp⟩
        · exact ⟨-(1 / 2), h, -1, by push_cast; ring⟩
      rw [D.naut.infG_tw _ _ τ s hs]
      refine ⟨(hnd τ).map (add_left_injective s), fun z hz => ?_⟩
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨k, hk⟩ := hint τ y hy
      refine ⟨k + k0 + m + 1, ?_⟩
      have hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = 2 * (m : ℂ) + 1 := by
        exact_mod_cast hm
      push_cast at hm' ⊢
      rw [hk0]
      linear_combination hk + (1 / 2 : ℂ) * hm'
    exact (_root_.UpperTheory.GalN.tempo' hT p.a _ ha1 (D.naut.csd_tw _ _ hAut.1.1 hcsd) hr w).part_tw hAut hu α hα
end GlobalTheory.PartUnitary
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReductionTrivialOnWildInertia
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rbar_wild_inertia_of_labTame_repAtGN : ∀ (D : D7), GlobalTheory.RowCopy.RbarTie D → _root_.UpperTheory.GalS.LabTameS D.nd D.naut → _root_.UpperTheory.GalS.RowRepAtGN D → ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (i : D.nd.Loc), D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ → ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)), s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)) → D.ntypes.rbar σ (D.nd.w i) s = 1 := by
  first | exact @_root_.GlobalTheory.RowWildTame.main_alt | exact _root_.GlobalTheory.RowWildTame.main_alt | (intros; apply _root_.GlobalTheory.RowWildTame.main_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResidualCharpolyEq
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
theorem residual_charpoly_eq_alt_alt (hC : GlobalTheory.TwSys.Cheb) (D : D7) (h32 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (i : D.nd.Loc)
    (rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i rep)
    (x π : D.nd.X i) (ρx ρ0 : GE D.nd →* GL (Fin D.R.r) (D.nd.O i))
    (hx : ∃ e, IsDecomp (t := D.R.t) (rep x) ρx (D.nd.chi i) e)
    (r0 : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) (hr0 : IsHeckeGalois D.nd i π r0)
    (h0 : ∃ e, IsDecomp (t := D.R.t) r0 ρ0 (D.nd.chi i) e) (g : GE D.nd) :
    ((mat ρx g).map (IsLocalRing.residue (D.nd.O i))).charpoly =
      ((mat ρ0 g).map (IsLocalRing.residue (D.nd.O i))).charpoly := by
  classical
  have hG3 := (_root_.UpperTheory.GalS.g3' ((h32 i).2.2 rep hr).2.2.1).2 x π g
  obtain ⟨ex, hex⟩ := hx
  obtain ⟨e0, he0⟩ := h0
  have dx := charpoly_of_decomp D i rep (fun _ => ρx) x ⟨ex, hex⟩ g
  have d0 := charpoly_of_decomp D i (fun _ => r0) (fun _ => ρ0) π ⟨e0, he0⟩ g
  have hc := charpoly_eq_of_isHeckeGalois hC D i rep hr π r0 hr0 g
  set res := IsLocalRing.residue (D.nd.O i)
  set P : (D.nd.O i)[X] := ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i))
  have hP : (P.map res) ≠ 0 := by
    apply Polynomial.Monic.ne_zero
    apply Polynomial.Monic.map
    exact Polynomial.monic_prod_of_monic _ _ fun c _ => Polynomial.monic_X_sub_C _
  have e1 : ((mat ρx g).map res).charpoly * P.map res = ((mat ρ0 g).map res).charpoly * P.map res := by
    rw [Matrix.charpoly_map, Matrix.charpoly_map, ← Polynomial.map_mul, ← Polynomial.map_mul]
    have ex' : (rO D.nd i rep x g).charpoly = (mat ρx g).charpoly * P := dx
    have e0' : (mat r0 g).charpoly = (mat ρ0 g).charpoly * P := d0
    rw [← ex', ← e0', ← hc, ← Matrix.charpoly_map, ← Matrix.charpoly_map]
    exact hG3
  exact mul_right_cancel₀ hP e1
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
end
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RxCrys
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
theorem rx_crys_alt_alt (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) (hl0 : D.nd.l i ≠ D.host.g 0) (hl1 : D.nd.l i ≠ D.host.g 1)
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) := by
  have h1 := (_root_.UpperTheory.GalS.g2a' ((h41 i).2.2 r hr).2.1 w hw hl0 hl1 x).1
  have h2 : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x))) :=
    ((D.loc_tie i w hw).2.1 D.R.nV (r x) (by simpa [rO] using (hr x).1)).1.1 h1
  exact GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw (D.nbr i w hw).LL C.LL C.le
    D.R.nV _ h2
end GlobalTheory.CrysChiOne
end
section
namespace Formalism.MainNotions.N
end Formalism.MainNotions.N
end
section
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
end
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SGalIso
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
theorem UpperTheory.GalS.galIsoN_of_tie0_adm2_adm7 : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D →
    ∀ i, UpperTheory.GalS.GalIsoN D.nd D.naut i := by
  intro D hT hG _ i P Pa hB
  obtain ⟨ρ, c, s, o, -⟩ := UpperTheory.GalS.isoRep D hT (_root_.UpperTheory.GalS.weak' hG) i P Pa hB
  exact ⟨ρ, c, s, o⟩
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypePrimeLemmasTheorem
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.TypePrimeCongruences
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
def TypePrimeHypothesesAlt (D : D7) : Prop := SumRepresentations.adm5 D ∧ _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D ∧ TypePrimeWildIdempotentChoice D
def TypePrimeLemmasStatement (D : D7) : Prop := _root_.Formalism.MainNotions.TypePrimeCongruences.TypePrimeHypothesesAlt D → TypePrimeChoiceConclusions D
end Formalism.MainNotions.TypePrimeCongruences
end
end
end

