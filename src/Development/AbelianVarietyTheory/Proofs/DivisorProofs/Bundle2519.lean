module

public import Mathlib
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositive
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.QkExtExistsG

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenComplexPointsCoveringGenericDegree
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace GlobalTheory.CoverDegProj

theorem etale_morphismRestrict {X Y : Scheme.{0}} (π : Y ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (hπU : IsAffineOpen (π ⁻¹ᵁ U)) (hét : (π.app U).hom.Etale) : Etale (π ∣_ U) := by
  haveI : IsAffine U := hU
  haveI : IsAffine (π ⁻¹ᵁ U) := hπU
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
    morphismRestrict_appLE]
  refine (Scheme.Hom.appLE_congr π _ (Scheme.Opens.ι_image_top U) (V' := π ⁻¹ᵁ U) ?_
    (fun φ => RingHom.Etale φ.hom)).2 ?_
  · rw [Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top]
  · rw [← Scheme.Hom.app_eq_appLE]; exact hét

theorem etale_pullback_coords_of_etale {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    (π : Y ⟶ X) (hπ : π ≫ p = q) (D : ℕ) (U : X.Opens) (hU : IsAffineOpen U)
    (hπU : IsAffineOpen (π ⁻¹ᵁ U)) (hét : (π.app U).hom.Etale) (W : X.Opens) (x : Fin D → Γ(X, W))
    (hW : IsAffineOpen W) (hx : (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x).Etale)
    (z : Y) (hzU : π z ∈ U) (hzW : π z ∈ W) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ z ∈ V ∧ ∃ h : V ≤ π ⁻¹ᵁ W,
      (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q V) (fun a => (π.appLE W V h).hom (x a))).Etale := by
  subst hπ
  have hE := etale_morphismRestrict π U hU hπU hét
  obtain ⟨f, g, hfg, hz⟩ := exists_basicOpen_le_affine_inter hU hW (π z) ⟨hzU, hzW⟩
  have hW'U : X.basicOpen f ≤ U := X.basicOpen_le f
  have hW'W : X.basicOpen f ≤ W := hfg ▸ X.basicOpen_le g
  have hW' : IsAffineOpen (X.basicOpen f) := hU.basicOpen f
  have hV : IsAffineOpen (π ⁻¹ᵁ X.basicOpen f) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact hπU.basicOpen _
  have hVU : π ⁻¹ᵁ X.basicOpen f ≤ π ⁻¹ᵁ U := fun y hy => hW'U hy
  have h : π ⁻¹ᵁ X.basicOpen f ≤ π ⁻¹ᵁ W := fun y hy => hW'W hy
  refine ⟨π ⁻¹ᵁ X.basicOpen f, hV, hz, h, ?_⟩

  have e1 : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (π ≫ p) (π ⁻¹ᵁ X.basicOpen f))
      (fun a => (π.appLE W _ h).hom (x a)) =
      (π.appLE W _ h).hom.comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x) := by
    rw [MvPolynomial.comp_eval₂Hom, GlobalTheory.CoverDeg.algX_comp p π W _ h]
  rw [e1]
  refine RingHom.Etale.stableUnderComposition _ _ hx ?_

  have e2 : π.appLE W (π ⁻¹ᵁ X.basicOpen f) h =
      X.presheaf.map (homOfLE hW'W).op ≫ π.appLE (X.basicOpen f) (π ⁻¹ᵁ X.basicOpen f) le_rfl := by
    rw [Scheme.Hom.map_appLE]
  rw [e2, CommRingCat.hom_comp]
  refine RingHom.Etale.stableUnderComposition _ _ (GlobalTheory.CoverDeg.etale_map_basicOpen hW g _ hfg hW'W) ?_

  have ha : IsAffineOpen (U.ι ⁻¹ᵁ X.basicOpen f) :=
    hW'.preimage_of_isOpenImmersion U.ι (by rw [Scheme.Opens.opensRange_ι]; exact hW'U)
  have hb : IsAffineOpen ((π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ X.basicOpen f)) :=
    hV.preimage_of_isOpenImmersion _ (by rw [Scheme.Opens.opensRange_ι]; exact hVU)
  have e3 : (π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ X.basicOpen f) ≤ (π ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ X.basicOpen f) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, morphismRestrict_ι]
  have := HasRingHomProperty.appLE @Etale (π ∣_ U) hE ⟨_, ha⟩ ⟨_, hb⟩ e3
  rw [morphismRestrict_appLE] at this
  refine (Scheme.Hom.appLE_congr π _ ?_ ?_ (fun φ => RingHom.Etale φ.hom)).1 this
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hW'U
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hVU

theorem exists_open_covering_charts : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, genericPoint X ∈ U ∧ (∀ y ∈ ptsIn p σ U, (ptMap π hπ σ ⁻¹' {y}).encard = (π.residueDegree (genericPoint Y) : ℕ∞)) ∧ (∀ z : CxPts q σ, ptMap π hπ σ z ∈ ptsIn p σ U → ∀ c : AlgChart p σ D, ptMap π hπ σ z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, ptMap π hπ σ w ∈ c.e.source ∧ c'.e w = c.e (ptMap π hπ σ w)) := by
  intro k _ X Y _ _ p q σ D hpP hqP π hπ hη hδ
  haveI : CharZero k := RingHom.charZero σ
  obtain ⟨U, hU, hxU, hV, he, hf, hr⟩ :=
    GlobalTheory.GenFinEtField.exists_affine_finite_etale_free k X Y p q hpP hqP π hπ hη hδ
  refine ⟨U, hxU, fun y hy => ?_, fun z hz c hc => ?_⟩
  · rw [GlobalTheory.encard_fibre_eq_encard_ringHom π hπ U hU hV σ y hy]
    exact GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank (π.app U).hom _ he hf hr _
  · set y := PtsOver.map π hπ (spMap σ) z with hy
    have hyc : y ∈ ptsIn p σ c.U := c.source_subset hc
    have hpt : ∀ W : X.Opens, y ∈ ptsIn p σ W → π (z.1 (IsLocalRing.closedPoint ℂ)) ∈ W := by
      intro W hW
      have := mem_ptsIn.1 hW
      exact this
    obtain ⟨V, hVa, hzV, h, hVe⟩ := etale_pullback_coords_of_etale π hπ D U hU hV he c.U c.x c.affine c.etale _ (hpt U hz) (hpt c.U hyc)
    obtain ⟨c'', hc'', hU'', hx''⟩ := AlgChart.exists_of_etale (σ := σ) hVa _ hVe (mem_ptsIn.2 hzV)
    have key : ∀ w ∈ c''.e.source, w ∈ ptsIn q σ V ∧
        ∀ a, c''.e w a = ev q σ V ((π.appLE c.U V h).hom (c.x a)) w := by
      rcases c'' with ⟨e, U', aff, x', et, ss, ae, ho⟩
      dsimp only at hU'' hx'' ⊢
      subst hU''
      have hx : x' = fun a => (π.appLE c.U U' h).hom (c.x a) := hx''
      subst hx
      exact fun w hw => ⟨ss hw, ae w hw⟩
    have hS : IsOpen (c''.e.source ∩ PtsOver.map π hπ (spMap σ) ⁻¹' c.e.source) :=
      (PtsOver.continuous_map π hπ (spMap σ)).continuousOn.isOpen_inter_preimage c''.e.open_source
        c.e.open_source
    refine ⟨c''.restr _ hS, ⟨hc'', hc'', hc⟩, fun w hw => ⟨hw.2.2, ?_⟩⟩
    have hw' : w ∈ c''.e.source := hw.1
    obtain ⟨hwV, hwe⟩ := key w hw'
    ext a
    change c''.e w a = c.e (PtsOver.map π hπ (spMap σ) w) a
    rw [hwe a, c.apply_eq _ hw.2.2 a]
    exact valR_appLE w.1 π h hwV _

end GlobalTheory.CoverDegProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenTranslationsMovingClosedPointsIntoOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_open_mul_mem : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (V : G.left.Opens), (∃ v ∈ V, G.hom v = closedPoint R) → ∀ s : Finset G.left, (∀ x ∈ s, G.hom x = closedPoint R ∧ IsClosed ({x} : Set G.left)) → ∃ O : G.left.Opens, (∃ u ∈ O, G.hom u = closedPoint R) ∧ ∀ (Ω : Type) [Field Ω] (t : Sp Ω ⟶ Sp R) (x a : Over.mk t ⟶ G), (∀ z, x.left z ∈ s) → (∀ z, a.left z ∈ O) → ∀ z, (x * a).left z ∈ V := by
  intro R _ _ _ G _ _ hG V hV s hs
  obtain ⟨v, hvV, hvc⟩ := hV
  set F : Set G.left := G.hom ⁻¹' {closedPoint R} with hFdef
  have hFc : IsClosed F := (isClosed_singleton_closedPoint R).preimage G.hom.continuous
  have hcond : ∀ p : (G ⊗ G).left, G.hom ((snd G G).left p) = G.hom ((fst G G).left p) := fun p => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    exact congrArg (fun h : (G ⊗ G).left ⟶ Sp R => h p) pullback.condition.symm
  have hsurj : ∀ x : G.left, G.hom x = closedPoint R → (snd G G).left '' ((fst G G).left ⁻¹' {x}) = F := by
    intro x hx
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      show G.hom _ = closedPoint R
      rw [hcond p, show (fst G G).left p = x from hp, hx]
    · intro hw
      obtain ⟨p, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := G.hom) x w (hx.trans hw.symm)
      exact ⟨p, h1, h2⟩
  have hmu : ∀ p : (G ⊗ G).left, G.hom (μ[G].left p) = G.hom ((fst G G).left p) := fun p => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Over.w μ[G]]
    rfl
  let Ψ : G ⊗ G ⟶ G ⊗ G := lift (fst G G) ((fst G G)⁻¹ * snd G G)
  have hΨ1 : Ψ ≫ fst G G = fst G G := lift_fst _ _
  have hΨ2 : Ψ ≫ μ[G] = snd G G := by
    show fst G G * ((fst G G)⁻¹ * snd G G) = snd G G
    exact mul_inv_cancel_left _ _
  have hmsurj : ∀ x : G.left, G.hom x = closedPoint R → μ[G].left '' ((fst G G).left ⁻¹' {x}) = F := by
    intro x hx
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      show G.hom _ = closedPoint R
      rw [hmu p, show (fst G G).left p = x from hp, hx]
    · intro hw
      obtain ⟨q, hq, rfl⟩ := (hsurj x hx).symm ▸ hw
      refine ⟨Ψ.left q, ?_, ?_⟩
      · show (fst G G).left (Ψ.left q) = x
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hΨ1]; exact hq
      · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hΨ2]
  have hFirr : IsIrreducible F := by
    rw [← hsurj v hvc]
    exact (_root_.GlobalTheory.MoverFibre.isIrreducible_fibre_fst R G hG v).image _ (snd G G).left.continuous.continuousOn
  set gpt := hFirr.genericPoint
  have hgp : IsGenericPoint gpt F := by
    have := hFirr.isGenericPoint_genericPoint_closure
    rwa [hFc.closure_eq] at this

  have gen_of : ∀ (f : (G ⊗ G).left → G.left), Continuous f → ∀ (Z : Set (G ⊗ G).left) (ξ : (G ⊗ G).left),
      IsGenericPoint ξ Z → f '' Z = F → f ξ = gpt := by
    intro f hf Z ξ hξ hZ
    refine IsGenericPoint.eq ?_ hgp
    show closure {f ξ} = F
    apply le_antisymm
    · exact hFc.closure_subset_iff.2 (Set.singleton_subset_iff.2 (hZ ▸ ⟨ξ, hξ.mem, rfl⟩))
    · rw [← hZ, ← hξ.def, ← Set.image_singleton]
      exact image_closure_subset_closure_image hf
  let T : G.left → Set G.left := fun x =>
    (snd G G).left '' ((fst G G).left ⁻¹' {x} ∩ μ[G].left ⁻¹' (V : Set G.left)ᶜ)
  have hTc : ∀ x ∈ s, IsClosed (T x) := by
    intro x hx
    refine _root_.GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint R G hG x (hs x hx).1 (hs x hx).2 _ ?_ Set.inter_subset_left
    exact ((hs x hx).2.preimage (fst G G).left.continuous).inter
      (V.isOpen.isClosed_compl.preimage μ[G].left.continuous)
  have hgpV : gpt ∈ (V : Set G.left) := (hgp.specializes (show v ∈ F from hvc)).mem_open V.isOpen hvV
  have hgpT : ∀ x ∈ s, gpt ∉ T x := by
    intro x hx ⟨n, ⟨hn1, hn2⟩, hn3⟩
    have hZc : IsClosed ((fst G G).left ⁻¹' {x}) := (hs x hx).2.preimage (fst G G).left.continuous
    have hZi := _root_.GlobalTheory.MoverFibre.isIrreducible_fibre_fst R G hG x
    have hξ : IsGenericPoint hZi.genericPoint ((fst G G).left ⁻¹' {x}) := by
      have := hZi.isGenericPoint_genericPoint_closure
      rwa [hZc.closure_eq] at this
    have e2 := gen_of _ (snd G G).left.continuous _ _ hξ (hsurj x (hs x hx).1)
    have em := gen_of _ μ[G].left.continuous _ _ hξ (hmsurj x (hs x hx).1)
    have hnξ : hZi.genericPoint = n :=
      _root_.GlobalTheory.Mum.eq_of_specializes_of_fst_eq_of_snd_eq R G hG x (hs x hx).1 (hs x hx).2 _ _ hξ.mem hn1 (e2.trans hn3.symm) (hξ.specializes hn1)
    exact hn2 (hnξ ▸ em ▸ hgpV)
  refine ⟨⟨(⋃ x ∈ (s : Set G.left), T x)ᶜ,
    isOpen_compl_iff.2 (s.finite_toSet.isClosed_biUnion hTc)⟩, ⟨gpt, ?_, hgp.mem⟩, ?_⟩
  · show gpt ∉ ⋃ x ∈ (s : Set G.left), T x
    simp only [Set.mem_iUnion, not_exists]
    exact fun x hx => hgpT x hx
  · intro Ω _ t x a hx ha z
    by_contra hz
    let q : Over.mk t ⟶ G ⊗ G := lift x a
    have h1 : (fst G G).left (q.left z) = x.left z := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
    have h2 : (snd G G).left (q.left z) = a.left z := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
    have h3 : μ[G].left (q.left z) = (x * a).left z := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left]; rfl
    have hO := ha z
    simp only [TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hO
    exact hO (x.left z) (hx z) ⟨q.left z, ⟨h1, by simp only [Set.mem_preimage, Set.mem_compl_iff, h3]; exact hz⟩, h2⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodScalarCoordinatePolarisedDataLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

namespace GlobalTheory.Mum.TensPol

theorem exists_tauCoord : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (a b : Q.X),
    ∃ k, Q.TauCoord a b k := by
  intro R _ _ _ Q a b
  obtain ⟨u, hu⟩ := DVR.exists_gen_of_local (V := R) Q.M.L Q.M.isLB (lamPts (Q.c a) (Q.c b)) negε
  have e : ∀ i, (toUnit (TK R)).left ≫ lamPts (Q.c a) (Q.c b) i =
      lamPts (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) i := by
    intro i
    fin_cases i
    · exact congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_mul (toUnit (TK R)) (Q.c a) (Q.c b))
    · rfl
    · rfl
    · exact congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_one (toUnit (TK R)))
  obtain ⟨t, ht, hv⟩ := exists_gen Q.M.isLB (φ' := fun i => (toUnit (TK R)).left ≫ lamPts (Q.c a) (Q.c b) i) (ε' := negε)
    (fun U _ h => by simp only [e]) (Q.tau a b) (Q.tau_gen a b)
  obtain ⟨c, hc⟩ := exists_unit_val_eq_mul Q.M.isLB ht
    (DVR.pullGen_isGen Q.M.L _ _ u hu (toUnit (TK R)).left)
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom c, u, hu, fun z J hJ => ?_⟩
  have ec : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom c) = c :=
    Units.ext (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))) _)
  rw [ec, ← hv _ _ z J hJ]
  refine Units.ext ((hc _ (𝟙 _) z J hJ).trans ?_)
  refine congrArg₂ (· * ·) (gs_unit _ z ⊤ trivial _) (congrArg Units.val ((val_pull hJ u _ (𝟙 _)).trans ?_))
  rw [Category.id_comp]

end GlobalTheory.Mum.TensPol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodsPulledDegenerationDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periods_pulled_degeneration_data : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (D₀ : DegPre R) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁), ∃ (β₂ : (G2 D₁.P.A).left ⟶ (G2 D₀.P.A).left) (w₀ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ D₀.P.A D₀.P.L).pull β₂)), IsSquare (GlobalTheory.PsiEvenPull.proj hD) β₂ ∧ w₀.IsGen ∧ ∀ a b z J J₁, Good D₀.P.L z J → Good D₁.P.L z J₁ → val (D₁.tau a b) (𝟙 _) z J₁ = lamVal w₀ (lift (toUnit (TK V) ≫ D₁.c a) (toUnit (TK V) ≫ D₁.c b)).left z J J₁ * val (hD.psiW.tau (hD.xe a) (hD.xe b)) hD.g z J := by
  first | exact @GlobalTheory.TauPullOn.tau_pull | exact GlobalTheory.TauPullOn.tau_pull | (intros; apply GlobalTheory.TauPullOn.tau_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsFramesThetaSectionGenericFibreMember
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

theorem exists_points_frames_theta : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1) (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧ (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) ∧ (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) ∧ ρ.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪
  have hj : (TFK (R := V) (FractionRing V)).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V))) = _
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  have gp := 𝔪.cart
  have hsq : ∀ a, (spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ≫ X₁.ρ.P.A.hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    intro a
    rw [Category.assoc, Over.w (X₁.ρ.pt a), hj]
    simp
  let x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) := fun a =>
    Over.homMk (gp.1.lift _ _ (hsq a)) (gp.1.lift_snd _ _ _)
  have hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left := fun a => gp.1.lift_fst _ _ _
  obtain ⟨rig, fr, hrig, -, hfr⟩ := GlobalTheory.exists_frames_move_through (T := baseOver (Sp X₁.S.R))
    (T' := TFK (R := V) (FractionRing V)) (h := spMap 𝔪.yK) gp 𝔪.wl_gen X₁.ρ.rig_gen hx X₁.ρ.fr_tors
  have hτ : (spMap 𝔪.yK : (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left) ≫
      (baseOver (Sp X₁.S.R)).hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    rw [hj]; simp
  obtain ⟨th, hth⟩ := GlobalTheory.ThetaPtMove.exists_secRel (T := TFK (R := V) (FractionRing V))
    (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB (a := 1) X₁.ρ.th₁
  refine ⟨x, fr, th, rig, hx, fun a => ⟨(hfr a).1.2.1, fun z J J' hJ hJ' => ?_⟩, fun a => ?_, hrig, fun a => (hfr a).1⟩
  · have e := (hfr a).2 _ (𝟙 _) z J J' hJ hJ'
    rw [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at e
    exact e.symm
  · have hv := GlobalTheory.ThetaPtMove.isValueAt_move (T := TFK (R := V) (FractionRing V))
      (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) X₁.ρ.P.isLB 𝔪.A.isLB (a := 1)
      (x := x a) (x₀ := X₁.ρ.pt a) (hx a).symm (ρ₀ := X₁.ρ.fr a) (ρ := fr a) (hfr a).2 (s₀ := X₁.ρ.th₁) (s := th) hth
      (X₁.ρ.th_val a)
    intro z J hJ
    have e := GlobalTheory.FrameMove.sval_valueAt hv (𝟙 _) hJ
    rw [Category.id_comp] at e
    refine e.trans ?_
    rw [GlobalTheory.FrameMove.val_powFrame, Nat.cast_one, zpow_one]
    congr 1
    exact (gs_pull (𝟙 _) (spMap 𝔪.yK) z ⊤ trivial _).trans
      ((congrArg (fun q => gs q z ⊤ _) (Category.id_comp _)).trans (GlobalTheory.FrameMove.gs_spMap 𝔪.yK z _))

end GlobalTheory.Poinc.IntTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedE8ThetaPowerOverModuli
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegEighth

theorem exists_isSharpBasis (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) :
    ∃ bas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)), IsSharpBasis W bas := by
  have hS : (W + W.transpose).transpose = W + W.transpose := by
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have h1 : (W + W.transpose) * (W + W.transpose).adjugate = 1 := by rw [Matrix.mul_adjugate, hW.2, one_smul]
  have h2 : (W + W.transpose).adjugate * (W + W.transpose) = 1 := by rw [Matrix.adjugate_mul, hW.2, one_smul]
  let e : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
    { twistSnd (W + W.transpose).adjugate with
      invFun := twistSnd (W + W.transpose)
      left_inv := twistSnd_twistSnd _ _ h1
      right_inv := twistSnd_twistSnd _ _ h2 }
  refine ⟨(sharpReindex h).trans e, fun i j => ?_⟩
  rw [← sum_omegaStd_single h i j]
  exact sum_omegaStd_twistSnd _ _ hS h1 _ _

theorem exists_polAV_sharpOver : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∃ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))), P.g = 8 * g ∧ GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) ∧ rig.IsGen ∧ (letI := P.isAb.comm; HypS P.A P.L) := by
  intro g n _ hn hno F W hW
  have hn0 : n ≠ 0 := by omega
  let b := cycBase hn0
  let c : SiegPre g n (b.ζ : cycAway n) (𝟙 F.X ≫ F.s) := GlobalTheory.LowChart.siegPull F.univ (𝟙 F.X) (𝟙 F.X ≫ F.s) rfl
  have hc : c.Principal := GlobalTheory.LowChart.principal_siegPull F.univ _ _ rfl F.princ
  have hd : SmoothOfRelativeDimension g c.A.hom :=
    SiegSharpCover.smoothDim c (by omega) b.ζ.isUnit b.unit
  have hpow : b.ζ ^ n = 1 :=
    Units.ext ((Units.val_pow_eq_pow_val _ _).trans (Subtype.ext (Complex.isPrimitiveRoot_exp n hn0).pow_eq_one))
  obtain ⟨L₁, L₂⟩ := abelianSchemeLaws_all
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsLocallyNoetherian (Sp (cycAway n)) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of _)))
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : IsLocallyNoetherian F.X := LocallyOfFiniteType.isLocallyNoetherian F.s
  obtain ⟨bas, hb⟩ := exists_isSharpBasis g W hW
  obtain ⟨a, w, w', hw, hw', hs⟩ := EighthPowerFactor.exists_matrices hW.2
  obtain ⟨t, ⟨pr, hpr, hu, hL, -, -⟩, hp⟩ := GlobalTheory.exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB g (8 * g) W _ a w w'
    bas hW hb hw hw' hs n (cycAway n) b F.X (𝟙 F.X ≫ F.s) c hpow hno hc hd
  obtain ⟨r, hr⟩ := t.rigid
  exact ⟨t.pol, r, rfl, ⟨c, GlobalTheory.LowChart.siegPB_siegPull F.univ _ _ rfl, pr, hpr, hu, hL⟩, hr,
    t.act w, t.act w', t.hom w, t.hom w', hp.1, hp.2.2, hp.2.1⟩

end GlobalTheory.SiegEighth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQkZeroOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem exists_qk_zero_over : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k →
    ∀ b : TF (R := V) F ⟶ D.P.A, b ^ k = 1 → ∃ p : QkPt D F k, p.y = 0 ∧ p.g.b = b := by
  intro V _ _ D hB F _ _ _ k hk b hb
  obtain ⟨J, hJ⟩ := good_pt D.P.isLB (default : PrimeSpectrum F)
  exact exists_qk_over (F := F) hJ hB hk 0 b (by rw [hb, cPoint_zero])

end GlobalTheory.TInj
end
end

