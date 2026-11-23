module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0228
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0021
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzBigDef
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0224
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameParamRecordLe
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0231
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodRef
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0232
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0140
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0134
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0147
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0187
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeEquiv
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0539
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0085
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0114

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MBlockParamH
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.One.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.SplitRead.BlockParam GlobalTheory.LocLanglands GlobalTheory.LocGL
open GlobalTheory.WeilDeligne (WD Weil ineIncl)
section Local
variable {k : Type} [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}
theorem charPol_unr_twist' {rc : ∀ n, Irr k n → WD h} (hrc : _root_.UpperTheory.One.M.RecLawsH rc) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ)
    (σ : Ine (F := E) B) (c : ℂ) (hc : (rc 1 (detIrr 1 χ hχ)).charPol (ineIncl h σ) = X - C c)
    (n : ℕ) (π : Irr k n) (hn : n = 1) (α : ℂˣ)
    (e : Nonempty (π.π.Equiv (detRep (Fin n) (χ * unrChar k α)))) :
    (rc n π).charPol (ineIncl h σ) = X - C c := by
  subst hn
  let u : Irr k 1 := detIrr 1 (unrChar k α) (isSmoothChar_of_isUnram (isUnram_unrChar k α))
  have he : detRep (Fin 1) (χ * unrChar k α) = twist u.π (detChar (Fin 1) χ) := by
    show _ = twist (detRep (Fin 1) (unrChar k α)) (detChar (Fin 1) χ)
    unfold detRep ofChar
    rw [twist_twist]
    rfl
  have h1 := _root_.UpperTheory.One.M.RecLawsH.twist hrc 1 χ (detIrr 1 χ hχ) u π (good_of_one _ rfl) ⟨.refl _⟩ (he ▸ e)
  rw [h1, charPol_lpChar_of_unr _ _ ((hrc.sph 1 u).2 (isSpherical_detRep (isUnram_unrChar k α))) σ c hc,
    hrc.dim, pow_one]
theorem split_local_of_blockVec {rc : ∀ n, Irr k n → WD h} (hB : BlockSplit k) (hrc : _root_.UpperTheory.One.M.RecLawsH rc) (hs : RecSupp rc)
    {r t : ℕ} {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (ht : IsTame χ) (π : Irr k (r + t)) (v : π.V) (hv : v ≠ 0)
    (hvb : IsBlockVec χ π.π v) (c : Ine (F := E) B → ℂ)
    (hc : ∀ σ, (rc 1 (detIrr 1 χ hχ)).charPol (ineIncl h σ) = X - C (c σ)) (γ : Ine (F := E) B)
    (hm : ((rc _ π).charPol (ineIncl h γ)).rootMultiplicity (c γ) ≤ t) :
    ∃ a b : WD h, rc _ π = a.lpSum b ∧ a.lpDim = r ∧ b.lpDim = t ∧ b.mono0 ∧
      ∀ σ, b.charPol (ineIncl h σ) = (X - C (c σ)) ^ t := by
  classical
  rcases hB r t χ π v hχ ht hv hvb with ⟨π₁, π₂, hsph, e⟩ | ⟨s, d, σ, hsupp, hcard⟩
  · have hg : GoodI π₂ := GlobalTheory.AVGood.good_of_isSpherical _root_.GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness _
      (fixed_ne_bot_of_equiv (equivRep ⟨π₂.V, π₂.π, π₂.smooth, π₂.irr⟩) hsph)
    have h1 := _root_.UpperTheory.One.M.RecLawsH.twist hrc t χ (detIrr 1 χ hχ) π₂ (twistIrr π₂ χ hχ) hg ⟨.refl _⟩ ⟨.refl _⟩
    have hu := (hrc.sph t π₂).2 hsph
    refine ⟨rc r π₁, rc t (twistIrr π₂ χ hχ), hrc.prod r t π₁ _ π e, hrc.dim _ _, hrc.dim _ _, ?_, fun σ => ?_⟩
    · rw [h1, WD.monomial_char_iff _ _ (hrc.dim _ _)]
      exact WD.unr_mono0 _ hu
    · rw [h1, charPol_lpChar_of_unr _ _ hu σ _ (hc σ), hrc.dim]
  · exfalso
    set U := {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))} with hU
    have hdvd : (X - C (c γ)) ^ U.toFinset.card ∣ (rc _ π).charPol (ineIncl h γ) := by
      rw [hs _ s π d σ hsupp, ← Finset.prod_const]
      refine dvd_trans (dvd_of_eq (Finset.prod_congr rfl fun a ha => ?_))
        (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ U.toFinset))
      obtain ⟨h1, α, e⟩ := Set.mem_toFinset.1 ha
      exact (_root_.UpperTheory.One.M.charPol_unr_twist' hrc hχ γ _ (hc γ) _ _ h1 α e).symm
    have := (le_rootMultiplicity_iff (WD.charPol_monic _ _).ne_zero).2 hdvd
    rw [Set.ncard_eq_toFinset_card'] at hcard
    omega
end Local
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem split_param_of_typeBlock : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A) (S : Reading T) (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w), BlockSplitAll H.E → _root_.GlobalTheory.SplitRead.LawsAlt S → SuppLaws S → TypeBlock S i w hw → (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))) → ∀ P : A.AV i, (A.inePol (A.locV i P w) (N.gam0 i w)).rootMultiplicity (iotaO N A i (chi1 N i (N.gam0 i w))) ≤ R.t → ∃ a b : A.LP w, A.locV i P w = A.lpSum a b ∧ A.lpDim a = R.r ∧ A.lpDim b = R.t ∧ A.mono0 b ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol b σ = (X - C (iotaO N A i (chi1 N i σ))) ^ R.t := by
  intro R H what₂ N A T S i w hw hB hL hS hT hchi P hm
  haveI : CharZero (w.adicCompletion H.E) := charZero_compl w
  obtain ⟨v, hv, hvb⟩ := hT.2 P
  have hμ := (S i w hw).mu_ok.1
  rw [T.inePol w _ _ (N.locNd_chebotarevPlace_mem i w), (S i w hw).locV, WD.inePol_of_mem_Ine _ (N.locNd_chebotarevPlace_mem i w)] at hm
  obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := _root_.UpperTheory.One.M.split_local_of_blockVec (hB w) (hL i w hw) (hS i w hw) hμ hT.1 _ v hv hvb
    (fun σ => iotaO N A i (chi1 N i σ.1)) (fun σ => by
      rw [← hchi σ.1 σ.2, T.inePol w _ _ σ.2, (S i w hw).locMu (detIrr 1 _ hμ) ⟨.refl _⟩,
        WD.inePol_of_mem_Ine _ σ.2]) ⟨_, N.locNd_chebotarevPlace_mem i w⟩ hm
  obtain ⟨a, rfl⟩ := (T.e w).surjective a
  obtain ⟨b, rfl⟩ := (T.e w).surjective b
  refine ⟨a, b, (T.e w).injective ?_, ?_, ?_, (T.mono0 w b).2 h4, fun σ hσ => ?_⟩
  · rw [(S i w hw).locV, h1, T.sum]
  · rw [← T.dim, h2]
  · rw [← T.dim, h3]
  · rw [T.inePol w _ _ hσ, WD.inePol_of_mem_Ine _ hσ, h5]
end UpperTheory.One.M
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MClassMapD
section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.SerSys
open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical
variable {g : ℕ} [Fact g.Prime]
end GlobalTheory.SerSys
end
end
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
theorem exists_isRc_isClassMapD_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (I : Ident D), ∃ rc : GlobalTheory.SerSys.Corr D, _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc ∧ ∀ k v, GlobalTheory.SerSys.IsClassMapD D.naut.lpDim (rc k v) := by
  intro hL D T I
  obtain ⟨rc, hrc⟩ := _root_.GlobalTheory.TypeRec.Model.exists_isRc_alt hL T I
  refine ⟨rc, hrc, fun k v n π hπ => ?_⟩
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  obtain ⟨σ, e⟩ := GlobalTheory.TypeRec.Model.exists_pull I k v π hπ
  refine ⟨?_, fun π' hπ' hg => ?_⟩
  · rw [← T.dim, hrc k v n σ π e]
    exact H.dim _
  · obtain ⟨σ', e', hσ'⟩ := GlobalTheory.SerSys.LabDepth.exists_pull D I k v π' hπ' hg
    have hg' : UpperTheory.Zero.LLC.Good (GlobalTheory.LocLanglands.cls σ') :=
      haveI := charZero_compl (D.naut.plGw k v)
      good_cls_of_fixed ⟨_, ⟨D.host.g_prime k⟩, I.i k v, I.cont k v⟩ σ' hσ'
    constructor
    · intro hr
      have h2 := congrArg (T.e _) hr
      rw [hrc k v n σ π e, hrc k v n σ' π' e'] at h2
      obtain ⟨f⟩ := pull_iso_of_cls_eq I k v σ σ' (_root_.UpperTheory.One.M.LawsM.inj H _ _ hg' h2)
      exact ⟨e.some ≪≫ f ≪≫ e'.some.symm⟩
    · rintro ⟨f⟩
      apply (T.e _).injective
      rw [hrc k v n σ π e, hrc k v n σ π' ⟨f.symm ≪≫ e.some⟩]
end UpperTheory.One.M
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
namespace DiscreteGroups.sglob.DzType.Rt
open GlobalTheory.TypeRec GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem typeLab_of_local_m_alt : Green → GlobalTheory.Published.ZelevinskyPolynomialRing → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), GlobalTheory.HeightCounting.LabTrue D T → _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → GlobalTheory.SerSys.LabTie D L → (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) → GlobalTheory.LabPin.TypeLab D rep := by
  intro hG hZ hDZ hL D T Rw rep L hLab hRow hDep hLT hTame
  obtain ⟨I⟩ := _root_.GlobalTheory.TypeIdent.nonempty_ident D
  obtain ⟨rc, hrc, hcls⟩ := _root_.UpperTheory.One.M.exists_isRc_isClassMapD_alt hL D T I
  obtain ⟨cp, hcomp, hcp⟩ := _root_.GlobalTheory.T.exists_comp_irrSm_locR_eq_rc hL D T I rc hrc Rw rep hRow hDep
  have hP : DiscreteGroups.sglob.DzType.Rt.LabParamLe D.R.nV D L rc := DiscreteGroups.sglob.DzType.Rt.labParamLe_of D L rc hG (_root_.GlobalTheory.T.tame_gen_support_compat_of_is_rc hZ hL D T I rc hrc)
    (fun k => GlobalTheory.T.depthZeroSupercuspidal_cuspidalModule (D.host.g k))
    (fun k v => by
      obtain ⟨κ, hκ⟩ := hTame k v
      exact _root_.DiscreteGroups.sglob.DzType.Rt.tame_param_le_of_tame_coupled hDZ hL D T I rc hrc L k v κ hκ)
  have hfix : ∀ σ k v, fixK1 (cp σ k v).ρ ≠ ⊥ := by
    intro σ k v
    obtain ⟨s, τ, hsw, hloc, hfx⟩ := hDep σ k v
    have hT := hRow.1 σ s τ hloc
    have key : ∀ (w : PlE D.host) (hw : w = D.naut.plGw k v)
        (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (w.adicCompletion D.host.E))),
        T.e w (Rw.locR σ w) = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls τ) →
        GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (w.adicCompletion D.host.E) (Fin D.R.r)) ≠ ⊥ →
        fixK1 (cp σ k v).ρ ≠ ⊥ := by
      intro w hw τ hT hfx
      subst hw
      have h1 := hrc k v D.R.r τ (pull I k v τ) ⟨CategoryTheory.Iso.refl _⟩
      have h2 : rc k v D.R.r (pull I k v τ) = rc k v D.R.r (cp σ k v) := by
        rw [← (hcp σ k v).2]
        exact (T.e _).injective (h1.trans hT.symm)
      obtain ⟨e⟩ := (((hcls k v) D.R.r (cp σ k v) (hcp σ k v).1).2 (pull I k v τ) (GlobalTheory.TypeRec.Model.irrSm_pull I k v τ)
        (GlobalTheory.LabPin.principalCongruence_fixed_vector_rational_local_field I k v τ hfx)).1 h2.symm
      exact GlobalTheory.LabPin.principalCongruenceFixedVectors_ne_bot_of_iso e (GlobalTheory.LabPin.principalCongruence_fixed_vector_rational_local_field I k v τ hfx)
    exact key s.w hsw τ hT hfx
  intro σ k v
  have hlab : D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r (cp σ k v)) := by
    rw [Rw.lab_eq, (hcp σ k v).2]
  obtain ⟨h1, h2⟩ := _root_.DiscreteGroups.sglob.DzType.Rt.labLP_isLabel_and_actK_fix hG hL D T I rc L hrc hLab hLT hP k v (cp σ k v) (hcp σ k v).1 (hfix σ k v)
  show IsLabel D k (D.nd.lab k σ v) ∧ ∀ s : SplitPlace D.host.E, s.w = D.naut.plGw k v → SerFix (rep σ) s (D.ntypes.eSer k (D.nd.lab k σ v))
  rw [hlab]
  exact ⟨h1, fun s hs => _root_.GlobalTheory.DepthZeroSer.serFix_of_comp D I rep cp hcomp σ k v _ h2 s hs⟩
end DiscreteGroups.sglob.DzType.Rt
end
section
namespace GlobalTheory.LabPin
end GlobalTheory.LabPin
namespace GlobalTheory.LabPin
end GlobalTheory.LabPin
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MGoodRef
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M.B
end UpperTheory.One.M.B
open UpperTheory.One.M.B in
theorem UpperTheory.One.M.goodRef_alt :
    _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ _ _ a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real ≠ ⊥ → UpperTheory.One.M.GoodAU (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS) := by
  intro _ hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters
  refine GlobalTheory.LiftRef.overRows_and_mono levSplit levSplit (fun K B f T w Z Wt hX z p0 Y h' _ => ?_)
  intro Rw a M tup Q hMA _ j h1 h2 S hS hne s σ hσ
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st Z).toD7.R.m, i.1 + 1 = j := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hry : (M _ _ h1 h2).real y ≠ 0 := fun e =>
    hy0 ((M _ _ h1 h2).real_inj (e.trans (map_zero _).symm))
  obtain ⟨f', hf', hf0', hff'⟩ := GlobalTheory.AutUnr.exists_fixed_of_isoTyp _ hS.1.stable
    {κ | κ ∈ Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV ∧ TrivOutside {s.v} κ ∧ (s.v ∈ gPl (w.st Z).toD7 → IsPrincipalCongruenceAt s κ)} hy hry
    (fun κ hκ => GlobalTheory.SphInertRef.rt_real_eq_of_lev hMA i y κ (h' i (hMA.PV i) (hMA.std i) s κ hκ.1 hκ.2.1 hκ.2.2).1
      (h' i (hMA.PV i) (hMA.std i) s κ hκ.1 hκ.2.1 hκ.2.2).2)
  exact good_of_fix _ S hS s (fun hg => GlobalTheory.SplitTypeCompl.exists_padic_equiv _ s hg) f' hf' hf0'
    (fun κ a b c => hff' κ ⟨a, b, c⟩) σ hσ
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvCg
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr GlobalTheory.LayerMove
noncomputable section
namespace UpperTheory.One.M
set_option maxHeartbeats 4000000
def mvCg_alt (s : _root_.UpperTheory.One.M.TrivialCondition) {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE}
    (x : _root_.GlobalTheory.HeightCounting.CGTrueT hL D A.wdT) : _root_.GlobalTheory.HeightCounting.CGTrueT hL m.D (m.sideA_alt A).wdT :=
  @_root_.UpperTheory.One.M.New.cgMk _ _ _ s ((by with_unfolding_all exact (x.e :))) ((by with_unfolding_all exact ((_root_.UpperTheory.One.M.New.cgGood s x) :))) ((by with_unfolding_all exact ((_root_.UpperTheory.One.M.New.cgSurj x) :))) ((by with_unfolding_all exact (x.zero :))) ((by with_unfolding_all exact (x.loc :))) ((by with_unfolding_all exact (x.tw :))) ((by with_unfolding_all exact (x.inf :))) ((by with_unfolding_all exact (x.csd :)))
end UpperTheory.One.M
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDstA
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr GlobalTheory.LayerMove
noncomputable section
namespace UpperTheory.One.M
set_option maxHeartbeats 4000000
def stageAOfSwitch (s : _root_.UpperTheory.One.M.TrivialCondition) {D : D7} (N : TwNew D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cf : CharFrame D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf rep)
    (rep' : N.toD7.what₂.FT → NG.FinTyp N.toD7.host.E N.toD7.R.r) (e : HEq rep' rep) :
    _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL N.toD7 (N.cf cf) rep' where
  host := ⟨a.host.fr, a.host.jLL, a.host.embLL⟩
  jE := a.jE
  frame := a.frame
  A := _root_.GlobalTheory.HeightCounting.Up.LiTw.sideA_alt N a.A
  cg := _root_.UpperTheory.One.M.New.cgMk s a.cg.e (_root_.UpperTheory.One.M.New.cgGood s a.cg) (_root_.UpperTheory.One.M.New.cgSurj a.cg) a.cg.zero a.cg.loc a.cg.tw a.cg.inf a.cg.csd
  au := a.au
  row := by obtain rfl : rep' = rep := eq_of_heq e; exact a.row
  fr := ⟨a.fr.jE, a.fr.eOm, a.fr.comm⟩
  fr_jE := a.fr_jE
  pht := { a.pht with }
  depth := by obtain rfl : rep' = rep := eq_of_heq e; exact a.depth
  elem := { a.elem with }
  val := { a.val with }
  labc := a.labc
  zeta := a.zeta
  omax := a.omax
end UpperTheory.One.M
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MatrixRowsIntegralAtMember
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem rows_mem_ringOfIntegers_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => Function.Injective (Dof x).what₂.OtoLL ∧
    ∃ F : Subfield (Dof x).what₂.LL, ∀ y, y ∈ (Dof x).what₂.OtoLL.range ↔ y ∈ F ∧ IsIntegral ℤ y := by
  intro _
  refine Step.of_all fun K B f T _ _ _ _ w _ P x => ?_
  refine ⟨B.OtoLL_injective, B.Ks.toSubfield, fun y => ?_⟩
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨((show B.O from z) : B.Ks).2, B.O_int z⟩
  · rintro ⟨hy, hi⟩
    exact B.O_full y hy hi
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integer_embedding_injective_range_integral_of_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => Function.Injective (Dof x).what₂.OtoLL ∧ ∃ F : Subfield (Dof x).what₂.LL, ∀ y, y ∈ (Dof x).what₂.OtoLL.range ↔ y ∈ F ∧ IsIntegral ℤ y := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.rows_mem_ringOfIntegers_alt | exact _root_.GlobalTheory.HeightCounting.Up.rows_mem_ringOfIntegers_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.rows_mem_ringOfIntegers_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemMatrixGroupIdentityFrame
section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000
namespace GlobalTheory.MtId
variable {D : D7}
section Fam
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
variable {I0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Fam
section Asm
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Asm
section Cols
open GlobalTheory.Mem.Col2
variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px)
end Cols
section State
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
variable {P : Pre2 K w} (x : St P)
theorem exists_matrix_input_identity_frame_of_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ w P x =>
    ∃ m : InMt x.r.Y (cfOf x) w.I.xi (QOf P), ∀ i, GlobalTheory.MtRead.IdFrame x.r.Y.hF (m.ad.PV i) :=
  fun _ => by
    unfold AllSt
    exact StepW.of_all fun _ _ _ _ _ _ _ hs _ x => hs.1.elim fun pin => inMt_state x pin
end State
end GlobalTheory.MtId
end
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemRowJIffRTupStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_adapted_element_property_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → (κ ∈ rowJ W.S.X W.Q.instEq ↔ Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H) := by
  first | exact @_root_.GlobalTheory.LevZeroMem.mem_rowJ_iff_rTup_alt | exact _root_.GlobalTheory.LevZeroMem.mem_rowJ_iff_rTup_alt | (intros; apply _root_.GlobalTheory.LevZeroMem.mem_rowJ_iff_rTup_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemberAuxiliaryPrimeSplits
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.SplitPrimeAuxiliary
open scoped Pointwise
theorem exists_auxiliary_prime_split_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ v, v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  intro _ hL
  apply StepW.of_all
  intro K B f T w _ _ _ P x _ v hv
  rcases hv with hv | hv
  · exact isSplitPl_of_split B.host B.host.pde_prime B.toPre.pde_split.1 v hv
  · exact isSplitPl_of_split B.host B.host.pde'_prime B.toPre.pde_split.2 v hv
end GlobalTheory.SplitPrimeAuxiliary
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.places_over_pde_isSplitPl_of_levelC : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ v, v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  first | exact @_root_.GlobalTheory.SplitPrimeAuxiliary.exists_auxiliary_prime_split_alt | exact _root_.GlobalTheory.SplitPrimeAuxiliary.exists_auxiliary_prime_split_alt | (intros; apply _root_.GlobalTheory.SplitPrimeAuxiliary.exists_auxiliary_prime_split_alt <;> assumption)
end
end
end

