module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2418
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsSecNeObj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOriginValuesSumModPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem cst_id_eq_stalkOf {W : Type} [CommRing W] (z : Sp W) (a : W) : cst (𝟙 (Sp W)) z a = stalkOf z a :=
  gs_eq (𝟙 _) z ⊤ trivial _


open GlobalTheory.ExpansionValueZero in
theorem expandsAt_origVal : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (D' : DegData W (maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal W) D' A G) (k e : ℕ) (σ' : H0 U.LG.L k) (f' : ∀ x, D'.toPre.SecB k x) (w : D'.toPre.X → W), (∀ x, OrigVal D'.toPre (f' x) (w x)) → U.ExpandsAt e k σ' f' → ∃ S : Finset D'.toPre.X, (∀ x ∉ S, w x ∈ maximalIdeal W ^ (e + 1)) ∧ ∀ J', Good U.LG.L (cpt W) J' → ∃ c ∈ maximalIdeal W ^ (e + 1), sval σ' (unitW G) (cpt W) J' = stalkOf (cpt W) (∑ x ∈ S, w x + c) * (val U.LG.rig (idW W) (cpt W) J').val ^ k := by
  intro W _ _ _ D' A G _ _ U k e σ' f' w hw hE
  classical
  choose a ha using fun α => exists_value D'.toPre k α (f' α)
  obtain rfl : w = a := funext fun α => stalkOf_injective (cpt W) (by
    choose J hJ using fun ψ : Sp W ⟶ D'.toPre.P.A.left => exists_chart D'.toPre.P.isLB (ψ (cpt W))
    have h₁ := ha α _ (𝟙 (Sp W)) (cpt W) J hJ
    have h₂ := hw α (cpt W) J hJ
    rw [cst_id_eq_stalkOf] at h₁
    rw [← Units.val_pow_eq_pow_val] at h₂
    have h₃ : sval (f' α) (𝟙 (Sp W) ≫ eSec D'.toPre.P.A) (cpt W) J = sval (f' α) (unitW D'.toPre.P.A) (cpt W) J :=
      congrArg (fun q => sval (f' α) q (cpt W) J) (Category.id_comp (unitW D'.toPre.P.A))
    exact (Units.mul_left_inj _).1 (h₂.symm.trans (h₃.symm.trans h₁)))
  obtain ⟨x, hx⟩ := exists_coeff (A := W) U.LG.isLB σ' (eSec G) (GeneratorPullback.powGen U.LG.L _ _ U.LG.rig k)
    (DVR.powGen_isGen _ _ _ _ U.LG.rigGen k) (fun W _ f => by simp)
  have hx' : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (J), Good U.LG.L z J →
      sval σ' (r ≫ eSec G) z J = cst r z x * (val (L := U.LG.L) U.LG.rig r z J ^ k).val :=
    fun Z r z J hJ => (hx Z r z J hJ).trans (by rw [DVR.val_pow])
  obtain ⟨S, hS⟩ := value_sub_sum_mem U e k σ' f' hE x hx' w ha
  refine ⟨S, fun y hy => ?_, fun J' hJ' => ⟨x - ∑ α ∈ S, w α, hS S le_rfl, ?_⟩⟩
  · have h := Ideal.sub_mem _ (hS S le_rfl) (hS (insert y S) (Finset.subset_insert _ _))
    rw [Finset.sum_insert hy] at h
    convert h using 1
    ring
  · have h₁ := hx' _ (𝟙 (Sp W)) (cpt W) J' hJ'
    rw [cst_id_eq_stalkOf, Units.val_pow_eq_pow_val] at h₁
    rw [add_sub_cancel]
    exact (congrArg (fun q => sval σ' q (cpt W) J') (Category.id_comp (unitW G))).symm.trans h₁

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionTransportTranslationTwist
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.TwistedExpTransport


set_option maxHeartbeats 1600000 in
theorem expandsAt_twist : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (A A₂ : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U₂ : UnifPre I D₂ A₂ G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ⟶ D.toPre.P.A) (xe : D₂.toPre.X ≃+ D.toPre.X) (w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε)) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])) (e : ℕ) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0 → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.gv w (r ≫ (U₂.gt e).pG.left) z (fun i => J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ (U₂.gt e).pG.left)) * Geo.Tor.gw (U₂.w e) r z (J' (r ≫ (U₂.gt e).pG.left)) (fun _ => N' (r ≫ (fstG I e G).left)) = Geo.Tor.gw (U.w e) (r ≫ h) z (J (r ≫ h ≫ (U.gt e).pG.left)) (fun _ => N (r ≫ h ≫ (fstG I e G).left)) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z (N (r ≫ (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' (r ≫ (fstG I e G).left)) * Geo.Tor.val ν (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.val ((U.gt e).t (xe χ)) (r ≫ h) z J = (∏ k, Geo.Tor.gv w (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) z (fun i => J ((r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k)) ^ Oinvε k) * Geo.Tor.val ((U₂.gt e).t χ) r z J' * Geo.Tor.val (g.s (xe χ)) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → ∀ (σ : H0 U.LG.L 1) (σ₂ : H0 U₂.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J') → U.ExpandsAt e 1 σ f → U₂.ExpandsAt e 1 σ₂ f₂ := by
  intro R _ _ I D D₂ A A₂ G _ _ U U₂ a g β xe w wL ν e h hG hp h1 h2 σ σ₂ f f₂ hσ hf hE
  classical
  have hu : (U₂.gt e).pG.left ≫ (toUnit D₂.toPre.P.A).left = (thickObj R I e G).hom ≫ thick R I e := by
    have e1 := Over.w (toUnit D₂.toPre.P.A)
    have e2 := Over.w (U₂.gt e).pG
    have e3 : (𝟙_ (Over (Spec (CommRingCat.of R)))).hom = 𝟙 _ := rfl
    rw [e3, Category.comp_id] at e1
    rw [e1, e2]
    rfl
  obtain ⟨S, hS⟩ := expandsAt_val U e 1 σ f hE
  refine expandsAt_of_val U₂ e 1 σ₂ f₂ (S.map xe.symm.toEquiv.toEmbedding) fun y J' hJ' => ?_
  choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  choose N hN using fun ψ : (thickObj R I e G).left ⟶ G.left => exists_chart U.LG.isLB (ψ y)
  have hN : Good U.LG.L y N := hN

  let ω : ((thickObj R I e G).left ⟶ D₂.toPre.P.A.left) → ((thickObj R I e G).left.presheaf.stalk y)ˣ :=
    fun ψ => gv w ψ y (fun i => J (ψ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' ψ)
  have hω := fun χ => GlobalTheory.ExpTrans.prod_fam U₂ e 1 ω χ
  have hF : ∀ χ, sval (f (xe χ)) (h ≫ pGl U e) y J *
      (val (g.s (xe χ)) ((thickObj R I e G).hom ≫ thick R I e) y J * val ν ((thickObj R I e G).hom ≫ thick R I e) y J).val =
      (∏ κ, ω (pGl U₂ e ≫ D₂.toPre.famφB χ κ) ^ DegPre.famε 1 κ).val * sval (f₂ χ) (pGl U₂ e) y J' := by
    intro χ
    have := hf χ _ (pGl U₂ e) y J J' hJ hJ'
    rw [hu] at this
    rw [hp]
    exact this
  have hT : ∀ χ, val ((U.gt e).t (xe χ)) h y J =
      (∏ k, ω (Oφl U₂ e χ k) ^ Oinvε k) * val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J' *
        val (g.s (xe χ)) ((thickObj R I e G).hom ≫ thick R I e) y J := by
    intro χ
    have := h2 χ _ (𝟙 _) y J J' hJ hJ'
    simp only [Category.id_comp] at this
    exact this
  refine ⟨fun χ hχ => ?_, fun jL' hL' => ?_⟩
  · have hi : xe χ ∉ S := fun hc => hχ (Finset.mem_map.2 ⟨xe χ, hc, xe.symm_apply_apply χ⟩)
    have z0 := (hS _ h y J hJ).1 _ hi
    have := hF χ
    rw [z0, zero_mul] at this
    exact (Units.mul_right_eq_zero _).1 this.symm
  · obtain ⟨N', hN', eN'⟩ := exists_good U₂.LG.L U₂.LG.isLB y (K := PUnit) (fun _ => fGl I G e) (fun _ => jL')
      (fun _ _ _ => rfl) (fun _ => hL')
    have eN : N' (fGl I G e) = jL' := eN' PUnit.unit
    have hL₁ : fGl I G e (h y) ∈ U.LG.L.U (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) := by
      have m := hN (h ≫ fGl I G e)
      have e' : N (h ≫ fGl I G e) = N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left) := congrArg N hG
      rw [e'] at m
      exact m
    have W' : ω (pGl U₂ e) * wv U₂ e (𝟙 _) y (J' (pGl U₂ e)) jL' =
        wv U e h y (J (h ≫ pGl U e)) (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) *
          gw wL (fGl I G e) y (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) jL' *
          val ν ((thickObj R I e G).hom ≫ thick R I e) y J := by
      have := h1 _ (𝟙 _) y J J' N N' hJ hJ' hN hN'
      simp only [Category.id_comp] at this
      rw [hG, eN] at this
      exact this
    have Sg : sv U 1 σ (h ≫ fGl I G e) y (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) =
        (gw wL (fGl I G e) y (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) jL').val * sv U₂ 1 σ₂ (fGl I G e) y jL' := by
      have := hσ _ (fGl I G e) y N N' hN hN'
      rw [sval_of σ _ y N (fun _ => N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (fun _ => by rw [Category.comp_id]),
        sval_of σ₂ _ y N' (fun _ => jL') (fun _ => by rw [Category.comp_id]; exact eN), eN] at this
      rw [hG]
      exact this
    have E := (hS _ h y J hJ).2 _ hL₁
    refine (ω (pGl U₂ e)).mul_right_inj.1 ?_
    have key : ∀ χ, (val ν ((thickObj R I e G).hom ≫ thick R I e) y J).val *
        (sval (f (xe χ)) (h ≫ pGl U e) y J * (val ((U.gt e).t (xe χ)) h y J).val) =
        (ω (pGl U₂ e)).val * (sval (f₂ χ) (pGl U₂ e) y J' * (val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J').val) := by
      intro χ
      have hF' := hF χ
      have hω' := congrArg Units.val (hω χ)
      simp only [Units.val_mul, pow_one] at hF' hω'
      rw [hT χ]
      simp only [Units.val_mul]
      linear_combination ((∏ k, ω (Oφl U₂ e χ k) ^ Oinvε k).val * (val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J').val) * hF' +
        (sval (f₂ χ) (pGl U₂ e) y J' * (val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J').val) * hω'
    have L1 : (ω (pGl U₂ e)).val * ((wv U₂ e (𝟙 _) y (J' (pGl U₂ e)) jL' ^ 1).val * sv U₂ 1 σ₂ (fGl I G e) y jL') =
        (val ν ((thickObj R I e G).hom ≫ thick R I e) y J).val *
          ∑ α ∈ S, sval (f α) (h ≫ pGl U e) y J * (val ((U.gt e).t α) h y J).val := by
      rw [← E, pow_one, pow_one, Sg, ← _root_.mul_assoc, ← Units.val_mul, W']
      simp only [Units.val_mul]
      ring
    rw [L1, Finset.sum_map, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    obtain ⟨χ, rfl⟩ := xe.surjective x
    have e₀ : xe.symm.toEquiv.toEmbedding (xe χ) = χ := xe.symm_apply_apply χ
    rw [e₀]
    exact key χ

end GlobalTheory.TwistedExpTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsAtOfCodimLeOneOverCompleteDVRs
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CodimOneExtend

theorem extAt_of_flat {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X XK XV XF : Scheme.{0}} {p : X ⟶ Sp R} {J : XK ⟶ X} {q : XK ⟶ Sp K}
    (H : IsPullback J q p (spMap (algebraMap R K))) (φ : XV ⟶ X) [Flat φ] (A : XF ⟶ XV)
    (hA : ∀ U, Function.Injective (A.app U).hom) (B : XF ⟶ XK) (w : B ≫ J = A ≫ φ) (W : X.Opens)
    (f : Γ(XK, J ⁻¹ᵁ W)) (s : Γ(XV, φ ⁻¹ᵁ W)) (h₂ : A ⁻¹ᵁ φ ⁻¹ᵁ W ≤ B ⁻¹ᵁ J ⁻¹ᵁ W)
    (hs : (A.appLE _ _ le_rfl).hom s = (B.appLE _ _ h₂).hom f) (v : XV) (hv : φ v ∈ W) :
    GenericExtend.ExtAt J W f (φ v) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hvU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hv W.isOpen
  have hUW : U ≤ W := hUW
  obtain ⟨a, ha, b, hb⟩ := loc_surj (nonZeroDivisors R) H hU (resG XK (J.preimage_mono hUW) f)
  have hb' : ∀ z, J z ∈ U → gs (𝟙 XK) z (J ⁻¹ᵁ U) ((J.app U).hom b) =
      cst (J ≫ p) z a * gs (𝟙 XK) z (J ⁻¹ᵁ W) f := fun z hz ↦ by
    rw [gs_pull (𝟙 XK) J z U hz, Category.id_comp, hb z hz, gs_res (𝟙 XK) z _ hz]
  have hw : ∀ t, J (B t) = φ (A t) := fun t ↦ by
    rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  have e : (φ.app U).hom b = constFn (φ ≫ p) _ a * resG XV (φ.preimage_mono hUW) s := by
    refine hA _ (fn_ext fun t ht ↦ ?_)
    have ht' : J (B t) ∈ U := by rw [hw]; exact ht
    have k := congrArg (B.stalkMap t).hom (hb' (B t) ht')
    rw [map_mul, ← gs_stalkMap B t _ ht', ← gs_stalkMap B t _ (hUW ht'), H1.cst_stalkMap, gs_pull B J t U ht',
      w] at k
    have k' := congrArg (gs (𝟙 XF) t _) hs
    rw [gs_appLE A _ _ _ (𝟙 XF) t (hUW ht), gs_appLE B _ _ _ (𝟙 XF) t (hUW ht), Category.id_comp,
      Category.id_comp] at k'
    rw [gs_pull (𝟙 XF) A t _ ht, gs_pull (𝟙 XF) A t _ ht, Category.id_comp, gs_mul A t _ ht,
      gs_pull A φ t U ht, gs_constFn _ _ A t ht, gs_res A t _ ht, k, k', reassoc_of% w]
  have hd : cst p (φ v) a ∣ gs (𝟙 X) (φ v) U b := by
    refine dvd_descend φ v ?_
    have k := congrArg (gs (𝟙 XV) v _) e
    rw [gs_pull (𝟙 XV) φ v U hvU, gs_mul (𝟙 XV) v _ hvU, gs_constFn _ _ (𝟙 XV) v hvU, Category.id_comp,
      Category.id_comp] at k
    rw [← gs_stalkMap φ v U hvU, H1.cst_stalkMap, k]
    exact dvd_mul_right _ _
  obtain ⟨t, ht⟩ := hd
  obtain ⟨U', hU', c, rfl⟩ := X.presheaf.exists_germ_eq t
  have hm : φ v ∈ U ⊓ U' := ⟨hvU, hU'⟩
  have e₁ : gs (𝟙 X) (φ v) (U ⊓ U') (resG X inf_le_left b) =
      gs (𝟙 X) (φ v) (U ⊓ U') (constFn p (U ⊓ U') a * resG X inf_le_right c) := by
    rw [gs_res (𝟙 X) (φ v) _ hm, gs_mul (𝟙 X) (φ v) _ hm, gs_res (𝟙 X) (φ v) _ hm, gs_constFn p _ (𝟙 X) (φ v) hm,
      Category.id_comp, ht, gs_eq (𝟙 X) (φ v) U' hU']
    rfl
  rw [gs_eq (𝟙 X) (φ v) _ hm, gs_eq (𝟙 X) (φ v) _ hm] at e₁
  obtain ⟨O, hO, i₁, i₂, e'⟩ := X.presheaf.germ_eq (φ v) hm hm _ _ e₁
  have le : O ≤ U ⊓ U' := i₁.le
  refine ⟨O, le.trans (inf_le_left.trans hUW), resG X (le.trans inf_le_right) c, hO, fn_ext fun z hz ↦ ?_⟩
  have hz' : J z ∈ U ⊓ U' := le hz
  have k := (gs_res J z le hz _).symm.trans ((congrArg (gs J z O) e').trans (gs_res J z le hz _))
  have k' : gs J z (U ⊓ U') (resG X inf_le_left b) =
      gs J z (U ⊓ U') (constFn p (U ⊓ U') a * resG X inf_le_right c) := k
  rw [gs_res J z _ hz', gs_mul J z _ hz', gs_res J z _ hz', gs_constFn p _ J z hz'] at k'
  have k₂ := hb' z hz'.1
  rw [gs_pull (𝟙 XK) J z U hz'.1, Category.id_comp, k'] at k₂
  have hu : IsUnit (cst (J ≫ p) z a) := by
    rw [H.w, cst_comp]
    refine IsUnit.of_mul_eq_one (cst q z (algebraMap R K a)⁻¹) ?_
    rw [← H1.cst_mul, mul_inv_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha), H1.cst_one]
  rw [gs_appLE J _ _ _ (𝟙 XK) z hz, Category.id_comp, gs_res J z _ hz, gs_res (𝟙 XK) z _ hz]
  exact hu.mul_left_cancel k₂

theorem exists_cDvr_flat (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CharZero R] (𝔭 : Ideal R) [𝔭.IsPrime] (h : 𝔭.height = 1) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V), GlobalTheory.LN.CDvr V ∧ ∃ φ : R →+* V,
      Function.Injective φ ∧ φ.Flat ∧ (IsLocalRing.maximalIdeal V).comap φ = 𝔭 := by
  have := ((GlobalTheory.normal_domain_height_one.{0, 0, 0} R (FractionRing R)).1 𝔭 h).1
  have hi : Function.Injective (algebraMap R (Localization.AtPrime 𝔭)) :=
    IsLocalization.injective _ 𝔭.primeCompl_le_nonZeroDivisors
  have : CharZero (Localization.AtPrime 𝔭) := charZero_of_injective_algebraMap hi
  obtain ⟨V, _, _, _, hV, j, hj, hl⟩ :=
    GlobalTheory.DvrCompletion.exists_cDvr_of_isDiscreteValuationRing (Localization.AtPrime 𝔭)
  refine ⟨V, _, _, _, hV, j.comp (algebraMap R _), hj.comp hi, ?_, ?_⟩
  · refine RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance) ?_
    let _ := j.toAlgebra
    have : FaithfulSMul (Localization.AtPrime 𝔭) V := (faithfulSMul_iff_algebraMap_injective _ _).2 hj
    exact (inferInstance : Module.Flat (Localization.AtPrime 𝔭) V)
  · rw [← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap]
    exact Localization.AtPrime.under_maximalIdeal

theorem exists_map_fractionRing {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V)
    (hφ : Function.Injective φ) : ∃ φK : FractionRing R →+* FractionRing V,
      φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ :=
  ⟨IsLocalization.map (M := nonZeroDivisors R) (T := nonZeroDivisors V) (FractionRing V) φ
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφ), IsLocalization.map_comp _⟩

theorem extAt_of_coheight_le_one : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (W : (Over.mk χ ⊗ G).left.Opens) (f : Γ((Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⊗ G).left, ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)), (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V) (φK : FractionRing R →+* FractionRing V) (h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ), φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ → ∃ s : Γ((Over.mk (spMap φ ≫ χ) ⊗ G).left, ((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W), ∀ (O : (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⊗ G).left.Opens) (h₁ : O ≤ ((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left ⁻¹ᵁ (((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)) (h₂ : O ≤ ((Over.homMk (spMap φK) h : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left ⁻¹ᵁ (((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)), (((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left.appLE _ O h₁).hom s = (((Over.homMk (spMap φK) h : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left.appLE _ O h₂).hom f) → ∀ y ∈ W, Order.coheight y ≤ 1 → y ∉ Set.range ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left → GlobalTheory.GenericExtend.ExtAt ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left W f y := by
  intro S G _ hG R _ _ _ _ _ χ W f hf y hy h1 hr
  have := hG.smooth
  have fl : ∀ T : Over S, Flat (fst T G).left := fun T ↦
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback T.hom G.hom).flip inferInstance
  have := fl (Over.mk χ)
  have H := ThetaRuleCompare.isPullback_whisker (A := G)
    (Over.homMk (spMap (algebraMap R (FractionRing R))) rfl :
      Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ)
  let x : PrimeSpectrum R := (fst (Over.mk χ) G).left y
  have hx1 : Order.coheight ((fst (Over.mk χ) G).left y) ≤ 1 := GenericExtend.coheight_apply_le_one _ h1
  have hx0 : x.asIdeal ≠ ⊥ := fun h0 ↦ hr (by
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback H y (⊥ : PrimeSpectrum (FractionRing R)) (by
      refine PrimeSpectrum.ext (h0.trans ?_)
      exact (Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))).symm)
    exact ⟨z, hz⟩)
  have hx : x.asIdeal.height = 1 := by
    refine le_antisymm ?_ (ENat.one_le_iff_ne_zero.2 fun h0 ↦ hx0 (Ideal.height_eq_zero_iff_eq_bot.1 h0))
    exact (idealHeight_eq_coheight (CommRingCat.of R) x).trans_le hx1
  obtain ⟨V, _, _, _, hV, φ, hφ, hfl, hc⟩ := exists_cDvr_flat R x.asIdeal hx
  obtain ⟨φK, hK⟩ := exists_map_fractionRing φ hφ
  have hK' : spMap φK ≫ spMap (algebraMap R (FractionRing R)) =
      spMap (algebraMap V (FractionRing V)) ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hK]
  obtain ⟨s, hs⟩ := hf V hV φ φK (by rw [reassoc_of% hK']) hK
  have HV := ThetaRuleCompare.isPullback_whisker (A := G)
    (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ)
  have HF := ThetaRuleCompare.isPullback_whisker (A := G)
    (Over.homMk (spMap (algebraMap V (FractionRing V))) rfl :
      Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ))
  have hφf : Flat (spMap φ) := Flat.SpecMap_iff.2 hfl
  have := MorphismProperty.of_isPullback (P := @Flat) HV.flip hφf
  have := fl (Over.mk (spMap φ ≫ χ))
  obtain ⟨v, rfl, -⟩ := Scheme.exists_preimage_of_isPullback HV y (IsLocalRing.closedPoint V)
    (PrimeSpectrum.ext hc.symm)
  have w : ((Over.homMk (spMap φK) (by simp only [Over.mk_hom]; rw [reassoc_of% hK']) :
      Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶
        Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left ≫
      ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl :
        Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left =
      ((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl :
        Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left ≫
      ((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← comp_whiskerRight, ← comp_whiskerRight]
    congr 2
    exact Over.OverMorphism.ext hK'
  have hA := Exist.CubicalExtension.app_injective_generic HF
  have h₂ := congrArg (· ⁻¹ᵁ W) w
  simp only [Scheme.Hom.comp_preimage] at h₂
  exact extAt_of_flat H _ _ hA _ w W f s h₂.ge (hs _ le_rfl h₂.ge) v hy

end GlobalTheory.CodimOneExtend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPeriodsProjectionPeriodPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

theorem GlobalTheory.Mum.Two.Fac.pt_ext (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (a b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (h : toUnit (TF (R := R) F) ≫ a = toUnit (TF (R := R) F) ≫ b) : a = b := by
  have : IsDominant (jK R) := isDominant_jK
  have : Surjective (jFK (R := R) F) := GlobalTheory.Balanced.surjective_spMap (algebraMap (FractionRing R) F)
  have : IsDominant (jFK (R := R) F) := inferInstance
  have : IsProper D.P.A.hom := D.P.isAb.proper
  have e := congrArg (fun m => m.left) h
  simp only [Over.comp_left] at e
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R)) D.P.A.hom
    ((Over.w a).trans (Over.w b).symm) (jFK (R := R) F ≫ jK R) ?_)
  simpa using e


open GlobalTheory.Mum.Two.Fac in
theorem GlobalTheory.Mum.Two.Fac.periods_of_factor : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R), D'.TauBimult → ∀ (O : Type) [Ring O] [StarRing O] [Module O D'.X] (o : D'.OAct O) (e f : O) (inc : D₀.P.A ⟶ D'.P.A) (pr : D'.P.A ⟶ D₀.P.A) (h : D₀.X →+ D'.X) (φ : D'.X →+ D₀.X), IsMonHom inc → IsMonHom pr → pr ≫ inc = o.onB.act e → (∀ χ, ∃ u : LB.Gen (CmpLB D' D₀ pr (h χ) χ), Nrm u) → LBIso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ o.onB.act f) : G2 D₀.P.A ⟶ G2 D'.P.A).left) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], (∀ (y : D'.X) (g : GtPtF D' F), GtPtF.IsIota y g → ∃ g' : GtPtF D₀ F, Act D' D₀ pr h g g' ∧ GtPtF.IsIota (φ y) g') → (∀ y, h (φ y) = star e • f • e • y) → (∀ y, D₀.c (φ y) = D'.c y ≫ pr) ∧ ∃ w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ o.onB.act f) : G2 D₀.P.A ⟶ G2 D'.P.A).left), w.IsGen ∧ ∀ y y' z J J', Good D'.P.L z J → Good D₀.P.L z J' → val (D₀.tau (φ y) (φ y')) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D₀.c (φ y)) (toUnit (TK R) ≫ D₀.c (φ y'))).left z J J' * val (D'.tau (e • y) (f • e • y')) (𝟙 _) z J := by
  intro R _ _ D₀ D' hB O _ _ _ o e f inc pr h φ hinc hpr hpi hu hw F _ _ hiota hh
  have hG := GlobalTheory.globalFns_holds
  have hi (y : D'.X) : ∃ g : GtPtF D' F, GtPtF.IsIota y g := GlobalTheory.TorusExt.exists_iota hB y
  have hc : ∀ y, D₀.c (φ y) = D'.c y ≫ pr := by
    intro y
    obtain ⟨g, hg⟩ := hi y
    obtain ⟨g', ha, hg'⟩ := hiota y g hg
    have h1 := ha.1
    rw [hg'.1, hg.1] at h1
    refine pt_ext R D₀ F _ _ ?_
    simpa only [Category.assoc] using h1
  refine ⟨hc, ?_⟩
  haveI := hinc
  haveI := hpr
  haveI : IsMonHom (o.onB.act f) := o.onB.hom f
  haveI : IsMonHom (o.onB.act e) := o.onB.hom e
  haveI : IsMonHom (o.onB.act (star e)) := o.onB.hom (star e)
  obtain ⟨w, hwg, hwn⟩ := _root_.GlobalTheory.Mum.Two.exists_lamVal_origin_two D₀.P.A D'.P.A D₀.P.L D'.P.L D₀.P.isLB D'.P.isLB inc (inc ≫ o.onB.act f) hw
  have hw1 := _root_.GlobalTheory.MumRigidZero.lamVal_one_left D₀.P.A D'.P.A D₀.P.L D'.P.L D₀.P.isLB D'.P.isLB D₀.P.isAb inc (inc ≫ o.onB.act f)
    w hwg hwn
  refine ⟨w, hwg, fun y y' z J J' hJ hJ' => ?_⟩
  obtain ⟨ur, hur, hur0⟩ := exists_ros hG D'.P.isAb D'.P.isLB (o.onB.act e) (o.onB.act (star e)) (o.onB.rosati e)
  have hur1 := _root_.GlobalTheory.RosZeroLeft.val_lift_one_left D'.P.A D'.P.L D'.P.isLB D'.P.isAb _ _ ur hur hur0
  obtain ⟨JN₀, hJN, hl, hr⟩ := exists_good_join D'.P.isLB D₀.P.isLB hJ hJ'
  obtain ⟨u, hun⟩ := hu (φ y')
  obtain ⟨g, hg⟩ := hi y
  obtain ⟨g', ha, hg'⟩ := hiota y g hg
  have A := _root_.GlobalTheory.Mum.Two.act_val_frac R D₀ D' pr h F y (φ y) _ g' hg hg' ha (φ y') u hun z JN₀ hJN
  rw [hl, hr] at A
  have B := val_corr hJ (o.tau_bal e ur hur hur0 y (f • e • y')) (𝟙 _)
  beta_reduce at B
  rw [val_mul hJ, val_pull hJ, Category.id_comp, ← hh y'] at B
  have hq : D₀.c (φ y') ≫ inc ≫ o.onB.act f = D'.c (f • e • y') := by
    rw [hc, o.c_lin, o.c_lin, ← hpi]; simp only [Category.assoc]
  have hq' : D'.c (h (φ y')) = D'.c (f • e • y') ≫ o.onB.act (star e) := by
    rw [hh y', o.c_lin]
  have C := _root_.GlobalTheory.Mum.Two.lam_eq_ros_mul_cmp R D₀ D' inc pr (o.onB.act e) (o.onB.act f) (o.onB.act (star e)) hpi w hwg hw1 ur hur hur1
    (h (φ y')) (φ y') (D'.c (f • e • y')) hq hq' u hun (TK R) (toUnit (TK R) ≫ D'.c y) z JN₀ hJN
  rw [hl, hr, Category.assoc, ← hc] at C
  rw [A, ← B, C]
  show _ = _ * _ * val (D'.tau (e • y) (f • e • y')) (𝟙 _) z J
  rw [mul_comm (val ur _ z J)]
  ac_rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem finite_coheight_one_notMem_open : ∀ (X : Scheme.{0}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (U : X.Opens), genericPoint X ∈ U →
    {z : X | Order.coheight z = 1 ∧ z ∉ U}.Finite := by
  intro X _ _ U hU
  classical
  obtain ⟨S, hS, hc, hi, hUn⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  refine (hS.image fun T => if h : IsIrreducible T then h.genericPoint else genericPoint X).subset
    fun z hz => ?_
  obtain ⟨hz1, hzU⟩ := hz
  obtain ⟨T, hT, hzT⟩ := mem_sUnion.1 (hUn.le (show z ∈ (U : Set X)ᶜ from hzU))
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos (hi T hT)]
  have hg := (hi T hT).isGenericPoint_genericPoint (hc T hT)
  have h₁ : z ≤ (hi T hT).genericPoint := hg.specializes hzT
  have h₂ : (hi T hT).genericPoint < genericPoint X := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have e' : _ = genericPoint X := (Specializes.antisymm e (genericPoint_specializes _)).eq
    have hm : (hi T hT).genericPoint ∈ (U : Set X)ᶜ := hUn.ge (mem_sUnion.2 ⟨T, hT, hg.mem⟩)
    exact hm (e' ▸ hU)
  by_contra hne
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e =>
    hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [hz1] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

end GlobalTheory.Mix
end

