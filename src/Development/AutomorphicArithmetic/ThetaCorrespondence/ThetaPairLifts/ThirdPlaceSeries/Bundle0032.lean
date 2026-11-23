module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0350
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0721
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0021
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSignatureDataSpan
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0723
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeOrthOfAvTied
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PickSpec
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.HeightCounting.RowRhoInt
end GlobalTheory.HeightCounting.RowRhoInt
namespace GlobalTheory.HeightCounting.RowRhoInt
theorem twistEx_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE),
    GalEx D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π →
      ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l),
        IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := _root_.GlobalTheory.T.exists_galois_rep_of_cuspidal_alt
end GlobalTheory.HeightCounting.RowRhoInt
namespace GlobalTheory.HeightCounting.RowRhoInt
theorem core_data_of_point (hA : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (hG : GalEx D) (hR : RowCusp D A.row) (hC : GlobalTheory.RowTie.ChebSplit D.nd)
    (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT)
    (hσ : ∃ k, 1 ≤ k ∧ k ≤ D.R.m ∧ D.what₂.isot k σ ≠ ⊥) (hg : D.nd.goodRow σ) :
    ∃ (L : Loc.FinExt l) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (PadicAlgCl l)),
      Continuous (fun g => ((ρ g : GL (Fin D.R.r) (PadicAlgCl l)) : Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl l))) ∧
      (∀ g i k, ((ρ g : GL (Fin D.R.r) (PadicAlgCl l)) : Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl l)) i k ∈
        Formalism.L2.TwC.intOf l L.1) ∧
      ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = A.row.locR σ w) →
        ∀ ι : Qbar l ≃+* ℂ, (∀ x, ι (j x) = embLL0 D x) →
          IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := by
  obtain ⟨k, hk1, hk2, hk⟩ := hσ
  obtain ⟨π₀, hc₀, hr₀, hl₀, hp₀⟩ := hR k hk1 hk2 σ hk hg
  obtain ⟨ι₀, hι₀⟩ := GlobalTheory.exists_padicAlgCl_ringEquiv_complex_comp_eq l ↥D.LL0 j (embLL0 D)
  have h0 : ∀ x, ι₀ (j x) = embLL0 D x := fun x => RingHom.congr_fun hι₀ x
  obtain ⟨ρG, hρG⟩ := _root_.GlobalTheory.HeightCounting.RowRhoInt.twistEx_alt hA D cf jE A hG l ι₀ π₀ hc₀ hr₀
  obtain ⟨L, P, hP⟩ := conjIntegral l (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) D.R.r ρG hρG.1
  let ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (PadicAlgCl l) := (MulAut.conj P⁻¹).toMonoidHom.comp ρG
  have hρ : ∀ g, ρ g = P⁻¹ * ρG g * P := fun g => by simp [ρ, MulAut.conj_apply]
  have hρ0 : IsRepOf D l ι₀ (D.naut.tw π₀ D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ :=
    isRepOf_conj D l ι₀ _ _ ρG ρ P hρ hρG
  refine ⟨L, ρ, hρ0.1, fun g i k => by rw [hρ]; exact hP g i k, fun π hc hr hl ι hι => ?_⟩
  have h1 := isRepOf_of_read D l ι₀ ι j h0 hι _ _ ρ hρ0 hp₀
  obtain ⟨ρ', hρ'⟩ := _root_.GlobalTheory.HeightCounting.RowRhoInt.twistEx_alt hA D cf jE A hG l ι π hc hr
  refine isRepOf_of_split D hC l ι _ _ _ ρ ρ' h1 hρ' (fun w hw => ?_)
  rw [D.naut.locG_tw, D.naut.locG_tw, hl₀ w hw, hl w hw]
end GlobalTheory.HeightCounting.RowRhoInt
namespace GlobalTheory.HeightCounting.RowRhoInt
section Pick
variable (hA : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE)
  (hG : GalEx D) (hR : RowCusp D A.row) (hC : GlobalTheory.RowTie.ChebSplit D.nd)
open Classical in
def pickL_alt (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT) : Loc.FinExt l :=
  if h : GoodOcc D σ then (_root_.GlobalTheory.HeightCounting.RowRhoInt.core_data_of_point hA D cf jE A hG hR hC l j σ h.1 h.2).choose else ⟨⊥, inferInstance⟩
open Classical in
def padicRepresentationOfEmbedding (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT) :
    Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (PadicAlgCl l) :=
  if h : GoodOcc D σ then (_root_.GlobalTheory.HeightCounting.RowRhoInt.core_data_of_point hA D cf jE A hG hR hC l j σ h.1 h.2).choose_spec.choose else 1
theorem pick_spec_alt (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT) (h : GoodOcc D σ) :
    Continuous (fun g => ((_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC l j σ g : GL (Fin D.R.r) (PadicAlgCl l)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl l))) ∧
    (∀ g i k, ((_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC l j σ g : GL (Fin D.R.r) (PadicAlgCl l)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l j σ).1) ∧
    ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = A.row.locR σ w) →
      ∀ ι : Qbar l ≃+* ℂ, (∀ x, ι (j x) = embLL0 D x) →
        IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC l j σ) := by
  simp only [_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt, _root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding, dif_pos h]
  exact (_root_.GlobalTheory.HeightCounting.RowRhoInt.core_data_of_point hA D cf jE A hG hR hC l j σ h.1 h.2).choose_spec.choose_spec
def bigOfStarStable (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) : Big D := fun l _ j =>
  ⟨⨆ σ : D.what₂.FT, ⨆ b : Bool, (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1, by
    haveI : ∀ σ b, FiniteDimensional ℚ_[l] ↥(_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1 :=
      fun σ b => (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).2
    haveI : ∀ σ : D.what₂.FT, FiniteDimensional ℚ_[l]
        ↥(⨆ b : Bool, (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1) :=
      fun σ => IntermediateField.finiteDimensional_iSup_of_finite
    exact IntermediateField.finiteDimensional_iSup_of_finite⟩
theorem pickL_jSide_le_cBig (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (l : ℕ) [Fact l.Prime]
    (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT) (b : Bool) :
    (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1 ≤ (_root_.GlobalTheory.HeightCounting.RowRhoInt.bigOfStarStable hA D cf jE A hG hR hC hstar l j).1 :=
  (le_iSup (fun b : Bool => (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1) b).trans
    (le_iSup (fun σ : D.what₂.FT => ⨆ b : Bool, (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1) σ)
end Pick
end GlobalTheory.HeightCounting.RowRhoInt
namespace GlobalTheory.HeightCounting.RowRhoInt
section HidaSetting
variable {D : D7} {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)} {T : TwR D.LL0 D.nd}
end HidaSetting
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem rho_rows_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE),
    GalEx D → RowCusp D A.row → GlobalTheory.RowTie.ChebSplit D.nd → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∃ c1 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
      (∀ (l : ℕ) [Fact l.Prime] j, (c1 l j).1 ≤ (b0 l j).1) →
      ∃ rho : RhoFam D T, (∀ i σ b, Continuous fun g =>
          ((rho i σ b g : GL (Fin D.R.r) (T.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (T.O0 i))) ∧
        ∀ i σ b, (∃ j, 1 ≤ j ∧ j ≤ D.R.m ∧ D.what₂.isot j σ ≠ ⊥) → D.nd.goodRow σ →
        ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = A.row.locR σ w) →
        ∀ (φ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ),
          (∀ z : ℤ_[T.l i], φ (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
            algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i])) →
          (∀ x : ↥D.LL0, ι (φ ((if b then T.emb0 i else T.emb0b i) x)) = embLL0 D x) →
          IsRepOf D (T.l i) ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2)
            (mapRep (φ.comp (algebraMap (T.O0 i) (FractionRing (T.O0 i)))) (rho i σ b)) := by
  intro hA D cf jE A hG hR hC hstar
  refine ⟨_root_.GlobalTheory.HeightCounting.RowRhoInt.bigOfStarStable hA D cf jE A hG hR hC hstar, fun b0 b1 Sx T Sp hc => ?_⟩
  classical
  have hmem : ∀ (i : T.Tw) (σ : D.what₂.FT) (b : Bool) (h : GoodOcc D σ) g k k',
      ((_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ g : GL (Fin D.R.r) (PadicAlgCl (T.l i))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl (T.l i))) k k' ∈ Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1 := by
    intro i σ b h g k k'
    exact intOf_mono (((_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_jSide_le_cBig hA D cf jE A hG hR hC hstar (T.l i) (Sp.j0 i) σ b).trans
      (hc (T.l i) (Sp.j0 i))).trans (Sp.ringSpec_baseExtension_lowerBound i))
      ((_root_.GlobalTheory.HeightCounting.RowRhoInt.pick_spec_alt hA D cf jE A hG hR hC (T.l i) _ σ h).2.1 g k k')
  let rho : RhoFam D T := fun i σ b =>
    if h : GoodOcc D σ then
      mapRep (Sp.eO0 i).symm.toRingHom (restrictRep (Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1)
        (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ) (hmem i σ b h))
    else 1
  have hemb : ∀ i, Topology.IsEmbedding (fun x : T.O0 i => kap Sp i (algebraMap (T.O0 i) (FractionRing (T.O0 i)) x)) :=
    fun i => (GlobalTheory.CoefEmbed.embedding_closed_integral (T.l i) (T.O0 i) (T.twistBaseCoefficientRing_isAdic i) (kap Sp i) (twistFractionFieldToPadicAlgebraicClosure_padicInt Sp i)).1
  have hks : ∀ i (y : Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1),
      kap Sp i (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((Sp.eO0 i).symm y)) = (y : PadicAlgCl (T.l i)) := by
    intro i y; rw [kap_alg, RingEquiv.apply_symm_apply]
  refine ⟨rho, fun i σ b => ?_, fun i σ b hocc hgood π hc hr hloc φ ι hφ hι => ?_⟩
  · by_cases h : GoodOcc D σ
    · have e : rho i σ b = mapRep (Sp.eO0 i).symm.toRingHom (restrictRep (Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1)
          (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ) (hmem i σ b h)) := dif_pos h
      rw [e]
      refine continuous_pi fun k => continuous_pi fun k' => ?_
      refine (hemb i).continuous_iff.mpr ?_
      have hc0 := (_root_.GlobalTheory.HeightCounting.RowRhoInt.pick_spec_alt hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ h).1.matrix_elem k k'
      refine hc0.congr fun g => ?_
      exact (hks i ⟨_, hmem i σ b h g k k'⟩).symm
    · have e : rho i σ b = 1 := dif_neg h
      rw [e]
      simp only [MonoidHom.one_apply, Units.val_one]
      exact continuous_const
  · have h : GoodOcc D σ := ⟨hocc, hgood⟩
    have e : rho i σ b = mapRep (Sp.eO0 i).symm.toRingHom (restrictRep (Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1)
        (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ) (hmem i σ b h)) := dif_pos h
    rw [e]
    have hstd : ∀ z : ℤ_[T.l i], algebraMap ℤ_[T.l i] (PadicAlgCl (T.l i)) z =
        algebraMap ℚ_[T.l i] (PadicAlgCl (T.l i)) (z : ℚ_[T.l i]) :=
      fun z => IsScalarTower.algebraMap_apply ℤ_[T.l i] ℚ_[T.l i] (PadicAlgCl (T.l i)) z
    haveI : FaithfulSMul ℤ_[T.l i] (T.O0 i) := by
      rw [faithfulSMul_iff_algebraMap_injective]
      intro z z' hzz
      have h3 := congrArg (fun y => kap Sp i (algebraMap (T.O0 i) (FractionRing (T.O0 i)) y)) hzz
      simp only [twistFractionFieldToPadicAlgebraicClosure_padicInt] at h3
      exact Subtype.ext ((algebraMap ℚ_[T.l i] (PadicAlgCl (T.l i))).injective h3)
    have h₀ : ((kap Sp i).comp (algebraMap (T.O0 i) (FractionRing (T.O0 i)))).comp (algebraMap ℤ_[T.l i] (T.O0 i)) =
        algebraMap ℤ_[T.l i] (PadicAlgCl (T.l i)) := RingHom.ext fun z => (twistFractionFieldToPadicAlgebraicClosure_padicInt Sp i z).trans (hstd z).symm
    have h₁ : (φ.comp (algebraMap (T.O0 i) (FractionRing (T.O0 i)))).comp (algebraMap ℤ_[T.l i] (T.O0 i)) =
        algebraMap ℤ_[T.l i] (PadicAlgCl (T.l i)) := RingHom.ext fun z => (hφ z).trans (hstd z).symm
    obtain ⟨τ, hτ⟩ := GlobalTheory.EmbConj.exists_algEquiv _ _ h₀ h₁
    have hφτ : ∀ q, φ q = τ (kap Sp i q) := by
      have : φ = (τ.toRingEquiv.toRingHom).comp (kap Sp i) :=
        IsLocalization.ringHom_ext (nonZeroDivisors (T.O0 i)) (RingHom.ext fun y => (hτ y).symm)
      intro q; rw [this]; rfl
    have hrep : mapRep (φ.comp (algebraMap (T.O0 i) (FractionRing (T.O0 i))))
        (mapRep (Sp.eO0 i).symm.toRingHom (restrictRep (Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1)
          (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ) (hmem i σ b h))) =
        mapRep τ.toRingEquiv.toRingHom (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ) := by
      ext g k k'
      change φ (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((Sp.eO0 i).symm ⟨_, hmem i σ b h g k k'⟩)) = τ _
      rw [hφτ, hks]
    rw [hrep]
    apply isRepOf_map D (T.l i) ι _ _ _ τ
    refine (_root_.GlobalTheory.HeightCounting.RowRhoInt.pick_spec_alt hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ h).2.2 π hc hr hloc _ (fun x => ?_)
    have hx := hι x
    cases b
    · have e1 : T.emb0b i x = T.emb0 i (starRestrictSubfield D hstar x) := T.restX_coefficientEmbedding_conj i x _ rfl
      simp only [Bool.false_eq_true, if_false] at hx
      rw [e1, hφτ, kap_emb0] at hx
      exact hx
    · simp only [if_true] at hx
      rw [hφτ, kap_emb0] at hx
      exact hx
end GlobalTheory.HeightCounting.RowRhoInt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameLocIffHeckeCongStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locations_distinguished_by_generics_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (i i' : L.X.nd.Loc), i ∈ L.X.nd.locs j w → i' ∈ L.X.nd.locs j w → ∀ (x : L.X.nd.X i) (x' : L.X.nd.X i'), (i = i' ↔ ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) - iotaO L.X.nd L.Y.naut i' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x') ∈ (A.pl.plB w).nonunits) := by
  first | exact @_root_.GlobalTheory.CoefDuty.sameLoc_iff_heckeCong_alt | exact _root_.GlobalTheory.CoefDuty.sameLoc_iff_heckeCong_alt | (intros; apply _root_.GlobalTheory.CoefDuty.sameLoc_iff_heckeCong_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SigDataExists
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.HeightCounting.FormsStep
section SigMake
variable (D : D7) (T : TwR D.LL0 D.nd) {S : RatDat D.ntw} (In : RatIn D S)
end SigMake
theorem span_eig_BI_alt (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T)
    (hst : HkStab D T S In) (hSb : In.Sb ⊆ Sx) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (hsp : ∀ i j b, Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) = ⊤)
    (i : T.Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    Submodule.span (FractionRing (T.O i))
      {y : FractionRing (T.O i) ⊗[T.O i] ↥(BI D T S In i j b) | ∃ σ : D.what₂.FT,
        (D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ) ∧ ∀ k P, sigVal D T i k P →
          (hkB D T S In hst i j b k P).baseChange (FractionRing (T.O i)) y = sigLam D T In i j b σ k P • y} = ⊤ := by
  obtain ⟨e, he_inj, he_rng, he_tm'⟩ : ∃ e : FractionRing (T.O i) ⊗[T.O i] ↥(BI D T S In i j b) →ₗ[FractionRing (T.O i)]
      FmT D T S i j b, Function.Injective e ∧ LinearMap.range e = V0T D T S In.rho In.chi In.θ i j b ∧
      ∀ (c : FractionRing (T.O i)) (x : ↥(BI D T S In i j b)), e (c ⊗ₜ[T.O i] x) = c • (x : FmT D T S i j b) :=
    _root_.GlobalTheory.baseChange_inf_lattice_eq_subspace (BsupT D T S i j b) (hsp i j b) (V0T D T S In.rho In.chi In.θ i j b)
  have hcomm : ∀ k P, sigVal D T i k P → ∀ y : FractionRing (T.O i) ⊗[T.O i] ↥(BI D T S In i j b),
      e ((hkB D T S In hst i j b k P).baseChange (FractionRing (T.O i)) y) = hkT D T S In i j b k P (e y) := by
    intro k P hv y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => rw [LinearMap.baseChange_tmul, he_tm', he_tm', map_smul, hkB_coe_of_val D T In hst i j b k P h1 h2 hv]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have key : V0T D T S In.rho In.chi In.θ i j b ≤ Submodule.map e (Submodule.span (FractionRing (T.O i))
      {y : FractionRing (T.O i) ⊗[T.O i] ↥(BI D T S In i j b) | ∃ σ : D.what₂.FT,
        (D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ) ∧ ∀ k P, sigVal D T i k P →
          (hkB D T S In hst i j b k P).baseChange (FractionRing (T.O i)) y = sigLam D T In i j b σ k P • y}) := by
    refine le_trans (_root_.GlobalTheory.T.lattice_in_isotypic_sup_alt D cf jE A S In b0 b1 Sx T Sp hSb hstar i j b h1 h2) ?_
    refine iSup₂_le fun σ hσ => ?_
    intro x hx
    obtain ⟨hx0, hx1⟩ := Submodule.mem_inf.mp hx
    rw [← he_rng] at hx0
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx0
    refine Submodule.mem_map_of_mem (Submodule.subset_span ⟨σ, hσ, fun k P hv => he_inj ?_⟩)
    rw [hcomm k P hv, map_smul]
    simp only [Submodule.mem_iInf] at hx1
    exact Module.End.mem_eigenspace_iff.mp (hx1 k P hv)
  rw [eq_top_iff]
  intro y _
  have hy : e y ∈ Submodule.map e _ := key (he_rng ▸ LinearMap.mem_range_self e y)
  obtain ⟨z, hz, hze⟩ := Submodule.mem_map.mp hy
  rw [← he_inj hze]
  exact hz
theorem sig_of_fg_alt (hfg : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool),
    (BsupT D T S i j b).FG ∧
      Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) = ⊤) : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T)
    (hst : HkStab D T S In), In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∃ sd : SigData D T,
      (∀ i j b, 1 ≤ j → j ≤ D.R.m →
        Submodule.span (FractionRing (T.O i))
          {x : TensorProduct (T.O i) (FractionRing (T.O i)) ↥(BI D T S In i j b) | ∃ s : sd.Sig i, sd.jS i s = j ∧
            sd.side i s = b ∧ ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i →
              ((hkB D T S In hst i j b k P).baseChange (FractionRing (T.O i))) x =
                algebraMap (T.O i) (FractionRing (T.O i)) (sd.hEig i s k P) • x} = ⊤) ∧
      (∀ i (s s' : sd.Sig i), sd.jS i s = sd.jS i s' → sd.side i s = sd.side i s' →
        (∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i → sd.hEig i s k P = sd.hEig i s' k P) → s = s') ∧
      (∀ i s, D.what₂.isot (sd.jS i s) (sd.rowS i s) ≠ ⊥ ∧ D.nd.goodRow (sd.rowS i s)) ∧
      (∀ i s k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i →
        algebraMap (T.O i) (FractionRing (T.O i)) (sd.hEig i s k P) =
          algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i (sd.side i s) P : T.O i) ^ k *
            readT D T i (sd.side i s) (In.eig (sd.jS i s) (sd.rowS i s) k P)) ∧
      ∀ i s P, sd.hEig i s 0 P = 1 := by
  intro D cf jE A S In b0 b1 Sx T Sp hst hSb hstar
  refine ⟨sigDataOf D T In, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j b h1 h2
    haveI : Module.Finite (T.O i) ↥(BI D T S In i j b) :=
      Module.Finite.iff_fg.mpr (fg_BI D T S In (fun i j b => (hfg D S In T i j b).1) i j b)
    rw [eq_top_iff, ← _root_.GlobalTheory.HeightCounting.FormsStep.span_eig_BI_alt D cf jE A S In b0 b1 Sx T Sp hst hSb hstar (fun i j b => (hfg D S In T i j b).2) i j b h1 h2]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨σ, hσ, hy⟩
    by_cases hy0 : y = 0
    · rw [hy0]
      exact Submodule.zero_mem _
    have hint : ∀ k P, sigVal D T i k P → ∃ a : T.O i,
        algebraMap (T.O i) (FractionRing (T.O i)) a = sigLam D T In i j b σ k P :=
      fun k P hv => eigenvalue_integral_of_baseChange _ y hy0 _ (hy k P hv)
    let x : SigIdx D T In i := ⟨(⟨j, Nat.lt_succ_of_le h2⟩, b, σ), h1, hσ.1, hσ.2, hint⟩
    refine Submodule.subset_span ⟨⟨sigSys D T In i x, x, rfl⟩, rfl, rfl, fun k P hk1 hk2 hsp hP => ?_⟩
    rw [hy k P ⟨hk1, hk2, hsp, hP⟩]
    congr 1
    exact (sigEig_on D T In i x k P ⟨hk1, hk2, hsp, hP⟩).symm
  · intro i s s' h1 h2 h3
    have e1 := sigDataOf_spec D T In i s
    have e2 := sigDataOf_spec D T In i s'
    apply Subtype.ext
    refine Prod.ext h1 (Prod.ext h2 ?_)
    funext k P
    by_cases hv : sigVal D T i k P
    · exact h3 k P hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
    · change s.1.2.2 k P = s'.1.2.2 k P
      rw [← e1, ← e2]
      change sigEig D T In i _ k P = sigEig D T In i _ k P
      rw [sigEig_off D T In i _ k P hv, sigEig_off D T In i _ k P hv]
  · intro i s
    have e1 := sigDataOf_spec D T In i s
    have hj : s.1.1 = (s.2.choose.1.1 : ℕ) := (congrArg Prod.fst e1).symm
    show D.what₂.isot s.1.1 s.2.choose.1.2.2 ≠ ⊥ ∧ D.nd.goodRow s.2.choose.1.2.2
    rw [hj]
    exact ⟨s.2.choose.2.2.1, s.2.choose.2.2.2.1⟩
  · intro i s k P hk1 hk2 hsp hP
    have e1 := sigDataOf_spec D T In i s
    have hj : s.1.1 = (s.2.choose.1.1 : ℕ) := (congrArg Prod.fst e1).symm
    have hb : s.1.2.1 = s.2.choose.1.2.1 := (congrArg (fun p => p.2.1) e1).symm
    have hh : s.1.2.2 = sigEig D T In i s.2.choose := (congrArg (fun p => p.2.2) e1).symm
    show algebraMap (T.O i) (FractionRing (T.O i)) (s.1.2.2 k P) =
      algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i s.1.2.1 P : T.O i) ^ k *
        readT D T i s.1.2.1 (In.eig s.1.1 s.2.choose.1.2.2 k P)
    rw [hh, hj, hb]
    exact sigEig_on D T In i _ k P ⟨hk1, hk2, hsp, hP⟩
  · intro i s P
    have e1 := sigDataOf_spec D T In i s
    have hh : s.1.2.2 = sigEig D T In i s.2.choose := (congrArg (fun p => p.2.2) e1).symm
    show s.1.2.2 0 P = 1
    rw [hh]
    exact sigEig_off D T In i _ 0 P (fun h => absurd h.1 (by omega))
theorem sigData_exists_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T)
    (hst : HkStab D T S In), In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∃ sd : SigData D T,
      (∀ i j b, 1 ≤ j → j ≤ D.R.m →
        Submodule.span (FractionRing (T.O i))
          {x : TensorProduct (T.O i) (FractionRing (T.O i)) ↥(BI D T S In i j b) | ∃ s : sd.Sig i, sd.jS i s = j ∧
            sd.side i s = b ∧ ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i →
              ((hkB D T S In hst i j b k P).baseChange (FractionRing (T.O i))) x =
                algebraMap (T.O i) (FractionRing (T.O i)) (sd.hEig i s k P) • x} = ⊤) ∧
      (∀ i (s s' : sd.Sig i), sd.jS i s = sd.jS i s' → sd.side i s = sd.side i s' →
        (∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i → sd.hEig i s k P = sd.hEig i s' k P) → s = s') ∧
      (∀ i s, D.what₂.isot (sd.jS i s) (sd.rowS i s) ≠ ⊥ ∧ D.nd.goodRow (sd.rowS i s)) ∧
      (∀ i s k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i →
        algebraMap (T.O i) (FractionRing (T.O i)) (sd.hEig i s k P) =
          algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i (sd.side i s) P : T.O i) ^ k *
            readT D T i (sd.side i s) (In.eig (sd.jS i s) (sd.rowS i s) k P)) ∧
      ∀ i s P, sd.hEig i s 0 P = 1 :=
  _root_.GlobalTheory.HeightCounting.FormsStep.sig_of_fg_alt bsupT_fg_span_all
end GlobalTheory.HeightCounting.FormsStep
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitOutOfStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_conductor_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ → ∀ e : L₁.lay.fixZ.nd.X i₁ ≃ L₀.lay.fixZ.nd.X i₀, (∀ (v : PlE D.host) (k : ℕ) (x : L₁.lay.fixZ.nd.X i₁), SplitOut L₁.lay.fixZ.nd i₁ v → 1 ≤ k → k ≤ D.R.nV → iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ ((L₁.lay.fixZ.nd.hT i₁ v k : L₁.lay.fixZ.nd.X i₁ → L₁.lay.fixZ.nd.O i₁) x) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ ((L₀.lay.fixZ.nd.hT i₀ v k : L₀.lay.fixZ.nd.X i₀ → L₀.lay.fixZ.nd.O i₀) (e x))) → ∀ x, x ∈ L₁.lay.fixZ.nd.Z i₁ ↔ e x ∈ L₀.lay.fixZ.nd.Z i₀ := by
  first | exact @_root_.GlobalTheory.ExtTheta.theta_loci_alt | exact _root_.GlobalTheory.ExtTheta.theta_loci_alt | (intros; apply _root_.GlobalTheory.ExtTheta.theta_loci_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeOrthOfPinStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_orthogonality_of_form' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, MtForm D P.M i → GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i := by
  first | exact @_root_.GlobalTheory.ThetaExh.typeOrth_of_pin_alt | exact _root_.GlobalTheory.ThetaExh.typeOrth_of_pin_alt | (intros; apply _root_.GlobalTheory.ThetaExh.typeOrth_of_pin_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeTameOfRamifiedStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_tame_of_tame_not_unram : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ i w hw, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → GlobalTheory.SplitWeil.IsTame (S i w hw).mu → ¬ GlobalTheory.SplitWeil.IsUnram (S i w hw).mu → TypeTame S i w hw := by
  first | exact @_root_.GlobalTheory.TypeTame.typeTame_of_ramified_alt | exact _root_.GlobalTheory.TypeTame.typeTame_of_ramified_alt | (intros; apply _root_.GlobalTheory.TypeTame.typeTame_of_ramified_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeVecBlockCharFixedPlaceStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_completion_iso_tame_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → IsTame (S i s.w hw).mu → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ Q, ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x f = blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
  exact _root_.GlobalTheory.typeVec_blockChar_fixedPlace_alt
end
end

