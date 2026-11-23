module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2507
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2494
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2492

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightPullbackResidueDegree
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProjFormulaVert


set_option maxHeartbeats 1000000 in
theorem exists_affine_finite_free (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (hX : IsProjOver p) (hY : IsProjOver q) (π : Y ⟶ X) (hπ : π ≫ p = q)
    (hg : π (genericPoint Y) = genericPoint X) (hδ : π.residueDegree (genericPoint Y) ≠ 0) :
    ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧
      (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧
        Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = π.residueDegree (genericPoint Y)) := by
  have hqP : IsProper q := by
    obtain ⟨N, j, _, hj⟩ := hY
    have := isProper_str k N
    exact hj ▸ inferInstance
  have : IsSeparated (π ≫ p) := hπ ▸ (inferInstance : IsSeparated q)
  have hsep : IsSeparated π := IsSeparated.of_comp π p
  have : LocallyOfFiniteType (π ≫ p) := hπ ▸ (inferInstance : LocallyOfFiniteType q)
  have hlft : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  have : IsLocallyNoetherian X := by
    obtain ⟨N, j, _, hj⟩ := hX
    have : LocallyOfFiniteType p := hj ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨U₀, hU₀, hxU₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint X))
  have hyU₀ : genericPoint Y ∈ π ⁻¹ᵁ U₀ := by
    show π (genericPoint Y) ∈ U₀
    rw [hg]; exact hxU₀
  obtain ⟨V₀, hV₀, hyV₀, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hyU₀
  haveI : Nonempty U₀ := ⟨⟨_, hxU₀⟩⟩
  haveI : Nonempty V₀ := ⟨⟨_, hyV₀⟩⟩
  letI : Algebra Γ(X, U₀) Γ(Y, V₀) := (π.appLE U₀ V₀ hVle).hom.toAlgebra
  haveI : IsNoetherianRing Γ(X, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  haveI : FaithfulSMul Γ(X, U₀) Γ(Y, V₀) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (GlobalTheory.appLE_injective_of_genericPoint_map π hg ⟨_, hyV₀⟩ hVle)
  haveI : Algebra.FiniteType Γ(X, U₀) Γ(Y, V₀) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType π hlft ⟨U₀, hU₀⟩ ⟨V₀, hV₀⟩ hVle
  haveI : Algebra.IsAlgebraic Γ(X, U₀) Γ(Y, V₀) := GlobalTheory.GenDegAlg.isAlgebraic_appLE π hg hδ hU₀ ⟨_, hyV₀⟩ hVle
  obtain ⟨a₁, ha₁, H₁⟩ := GlobalTheory.finite_away_of_isAlgebraic_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  obtain ⟨a₂, ha₂, H₂⟩ := GlobalTheory.free_away_mul_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  have ha : a₁ * a₂ ≠ 0 := mul_ne_zero ha₁ ha₂
  have hUU₀ : X.basicOpen (a₁ * a₂) ≤ U₀ := X.basicOpen_le _
  have hUa : IsAffineOpen (X.basicOpen (a₁ * a₂)) := hU₀.basicOpen _
  have hxU : genericPoint X ∈ X.basicOpen (a₁ * a₂) := by
    have hne : X.basicOpen (a₁ * a₂) ≠ ⊥ := fun h => ha ((basicOpen_eq_bot_iff _).1 h)
    obtain ⟨z, hz⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    exact ((genericPoint_spec X).mem_open_set_iff (X.basicOpen (a₁ * a₂)).isOpen).2
      ⟨z, trivial, hz⟩
  set U : X.Opens := X.basicOpen (a₁ * a₂) with hU_def
  set V : Y.Opens := Y.basicOpen (π.appLE U₀ V₀ hVle (a₁ * a₂)) with hV_def
  have hVV₀ : V ≤ V₀ := Y.basicOpen_le _
  have hVe : V = V₀ ⊓ π ⁻¹ᵁ U := Scheme.basicOpen_appLE π V₀ U₀ hVle _
  have hVU : V ≤ π ⁻¹ᵁ U := by rw [hVe]; exact inf_le_right
  have hVa : IsAffineOpen V := hV₀.basicOpen _
  have hyV : genericPoint Y ∈ V := by
    rw [hVe]; exact ⟨hyV₀, show π (genericPoint Y) ∈ U from hg ▸ hxU⟩
  letI iA : Algebra Γ(X, U₀) Γ(X, U) := (X.presheaf.map (homOfLE hUU₀).op).hom.toAlgebra
  letI iB : Algebra Γ(Y, V₀) Γ(Y, V) := (Y.presheaf.map (homOfLE hVV₀).op).hom.toAlgebra
  letI iAB : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V hVU).hom.toAlgebra
  letI iAB' : Algebra Γ(X, U₀) Γ(Y, V) := (π.appLE U₀ V (hVV₀.trans hVle)).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U₀) Γ(X, U) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.map_appLE hVU (homOfLE hUU₀).op).symm)
  haveI : IsScalarTower Γ(X, U₀) Γ(Y, V₀) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.appLE_map hVle (homOfLE hVV₀).op).symm)
  haveI hlA : IsLocalization.Away (a₁ * a₂) Γ(X, U) :=
    hU₀.isLocalization_of_eq_basicOpen _ (homOfLE hUU₀) rfl
  haveI hlB : IsLocalization.Away (algebraMap Γ(X, U₀) Γ(Y, V₀) (a₁ * a₂)) Γ(Y, V) :=
    hV₀.isLocalization_of_eq_basicOpen _ (homOfLE hVV₀) rfl
  have e2 : a₂ * a₁ = a₁ * a₂ := mul_comm _ _
  have hfin : Module.Finite Γ(X, U) Γ(Y, V) := H₁ a₂ Γ(X, U) Γ(Y, V) hlA hlB
  have hfree : Module.Free Γ(X, U) Γ(Y, V) :=
    H₂ a₁ Γ(X, U) Γ(Y, V) (by rw [e2]; exact hlA) (by rw [e2]; exact hlB)
  have hpre : π ⁻¹ᵁ U = V := GlobalTheory.preimage_eq_of_finite_appLE π hUa hVa ⟨_, hyV⟩ hVU hfin
  have key : ∀ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U), W = π ⁻¹ᵁ U →
      (letI := (π.appLE U W hW).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, W) ∧ Module.Finite Γ(X, U) Γ(Y, W)) →
      (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) := by
    rintro W hW rfl h
    rw [Scheme.Hom.app_eq_appLE]
    exact h
  obtain ⟨h1, h2⟩ := key V hVU hpre.symm ⟨hfree, hfin⟩
  exact ⟨U, hUa, hxU, hpre ▸ hVa, h1, h2,
    GlobalTheory.GenFinEtField.finrank_app_eq_residueDegree π hg hUa (hpre ▸ hVa) hxU⟩

end GlobalTheory.ProjFormulaVert

namespace GlobalTheory.ProjFormulaVert

theorem algebra_zmod_eq {l : ℕ} {R : Type} [CommRing R] (a b : Algebra (ZMod l) R) : a = b :=
  Algebra.algebra_ext a b fun r => congrFun (congrArg DFunLike.coe
    (RingHom.ext_zmod (@algebraMap _ _ _ _ a) (@algebraMap _ _ _ _ b))) r

theorem height_pull_vertical : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ),
    IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ),
    L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ (y : Y) (l : ℕ) [Fact l.Prime],
    Nonempty (Algebra (ZMod l) Γ(clo y, ⊤)) → h' y = (π.residueDegree y : ℝ) * h (π y) := by
  intro k _ X Y p q D E hX hY π hπ L h h' hh hh' y l _ ⟨instW⟩
  obtain ⟨g, hgc, hgen, hgdeg⟩ := _root_.GlobalTheory.MixHt.clo_restrict_dominant X Y π y
  have hδ : g.residueDegree (genericPoint (clo y)) = π.residueDegree y := by
    rw [hgdeg, cloι_genericPoint]

  have hinj : Function.Injective g.appTop.hom := by
    have := GlobalTheory.appLE_injective_of_genericPoint_map g hgen (U := ⊤) (V := g ⁻¹ᵁ ⊤)
      ⟨genericPoint (clo y), trivial⟩ le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at this
  haveI : Nonempty (⊤ : (clo y).Opens) := ⟨⟨genericPoint (clo y), trivial⟩⟩
  haveI : CharP Γ(clo y, ⊤) l :=
    charP_of_injective_algebraMap (algebraMap (ZMod l) Γ(clo y, ⊤)).injective l
  haveI : CharP Γ(clo (π y), ⊤) l := ⟨fun n => by
    rw [← CharP.cast_eq_zero_iff Γ(clo y, ⊤) l n, ← map_natCast g.appTop.hom n,
      map_eq_zero_iff _ hinj]⟩
  letI instZ : Algebra (ZMod l) Γ(clo (π y), ⊤) := ZMod.algebra _ l
  have hWp : IsProjOver (strHom (ZMod l) (X := (clo y))) :=
    GlobalTheory.FibreProj.isProjOver_closed_fibre k Y q E hY (clo y) (cloι y) l
  have hZp : IsProjOver (strHom (ZMod l) (X := (clo (π y)))) :=
    GlobalTheory.FibreProj.isProjOver_closed_fibre k X p D hX (clo (π y)) (cloι (π y)) l
  have hgs : g ≫ strHom (ZMod l) (clo (π y)) = strHom (ZMod l) (clo y) :=
    comp_strHom fun r => congrFun (congrArg DFunLike.coe
      (RingHom.ext_zmod (g.appTop.hom.comp (algebraMap (ZMod l) _)) (algebraMap (ZMod l) _))) r

  obtain ⟨⟨m, hm⟩, -, -, -, hcl, hgd⟩ := _root_.GlobalTheory.MixHt.hasDim_basic k Y q (isAmb_of_isArithVar hY)
  obtain ⟨⟨m', hm'⟩, -, -, -, hcl', hgd'⟩ := _root_.GlobalTheory.MixHt.hasDim_basic k X p (isAmb_of_isArithVar hX)
  obtain ⟨d, -, hd⟩ := hm y
  obtain ⟨d', -, hd'⟩ := hm' (π y)
  have hWd : topologicalKrullDim (clo y) = d :=
    (hgd (clo y) d).1 ((hcl (clo y) (cloι y) _ d).1 (by rw [cloι_genericPoint]; exact hd))
  have hZd : topologicalKrullDim (clo (π y)) = d' :=
    (hgd' (clo (π y)) d').1 ((hcl' (clo (π y)) (cloι (π y)) _ d').1 (by rw [cloι_genericPoint]; exact hd'))
  obtain ⟨hle, hiff⟩ := _root_.GlobalTheory.DimDeg.dim_le_and_residueDegree_ne_zero_iff k X Y p q (isAmb_of_isArithVar hX) (isAmb_of_isArithVar hY) π hπ y d d' hd hd'

  have e1 := hh'.vertical (clo y) (cloι y) (ZMod l) d hWd
  have e2 := hh.vertical (clo (π y)) (cloι (π y)) (ZMod l) d' hZd
  rw [cloι_genericPoint] at e1 e2
  have ej : (cloι y ≫ π) ≫ p = cloι y ≫ q := by rw [Category.assoc, hπ]
  have ei : (g ≫ cloι (π y)) ≫ p = g ≫ cloι (π y) ≫ p := Category.assoc _ _ _
  have t1 : topSelfIntersection (ZMod l) ((L.pull π hπ).B.pull (cloι y)) d = topSelfIntersection (ZMod l) (L.B.pull (cloι y ≫ π)) d :=
    topSelf_congr (ZMod l) ((L.pull π hπ).pull (cloι y) rfl).isLB (L.pull (cloι y ≫ π) ej).isLB
      (LBIso.chartPull (chartPullLinComb L.B π (fun _ : PUnit => cloι y)
        (fun _ => cloι y ≫ π) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
        (chartPullId _) (PolBaseChange.lbIso_refl (LB.isLB_pull L.isLB _))) d
  have t2 : topSelfIntersection (ZMod l) (L.B.pull (g ≫ cloι (π y))) d =
      topSelfIntersection (ZMod l) ((L.B.pull (cloι (π y))).pull g) d :=
    topSelf_congr (ZMod l) (L.pull (g ≫ cloι (π y)) ei).isLB ((L.pull (cloι (π y)) rfl).pull g rfl).isLB
      (LBIso.symm (LBIso.chartPull (chartPullLinComb L.B (cloι (π y)) (fun _ : PUnit => g)
        (fun _ => g ≫ cloι (π y)) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
        (chartPullId _) (PolBaseChange.lbIso_refl (LB.isLB_pull L.isLB _)))) d
  rw [t1, ← hgc, t2] at e1
  rw [e1, e2]
  suffices key : topSelfIntersection (ZMod l) ((L.B.pull (cloι (π y))).pull g) d =
      (π.residueDegree y : ℤ) * topSelfIntersection (ZMod l) (L.B.pull (cloι (π y))) d' by
    rw [key]; push_cast; ring
  have hB : (L.B.pull (cloι (π y))).IsLB := (L.pull (cloι (π y)) rfl).isLB
  have hBg : ((L.B.pull (cloι (π y))).pull g).IsLB := ((L.pull (cloι (π y)) rfl).pull g rfl).isLB
  have hclo : topologicalKrullDim (closure ({g (genericPoint (clo y))} : Set (clo (π y)))) = d' := by
    rw [hgen, (genericPoint_spec (clo (π y))).def]
    exact (Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq.trans hZd
  by_cases h0 : π.residueDegree y = 0
  · have hne : d ≠ d' := fun e => (hiff.2 e) h0
    have hlt : d' < d := lt_of_le_of_ne hle (Ne.symm hne)
    have hz := GlobalTheory.PullVanish.interNum_pull_eq_zero (ZMod l) 0 d (clo y) (clo (π y)) hWp
      (by rw [Nat.zero_add, hWd]) g (by rw [hclo]; exact_mod_cast hlt)
      (fun i => i.elim0) (fun i => i.elim0) (fun _ => L.B.pull (cloι (π y))) (fun _ => hB)
    rw [h0, Nat.cast_zero, zero_mul, topSelf_def, ← interNum_comp_equiv (ZMod l) _ (fun _ => hBg)
      (Equiv.emptySum (Fin 0) (Fin d)), ← hz]
    congr 1
    funext x
    rcases x with i | a
    · exact i.elim0
    · rfl
  · have hdd : d = d' := hiff.1 h0
    subst hdd
    obtain ⟨U, hU, hgU, hU', hfree, hfin, hrank⟩ := exists_affine_finite_free (ZMod l) (clo (π y)) (clo y)
      (strHom (ZMod l) (clo (π y))) (strHom (ZMod l) (clo y)) hZp hWp g hgs hgen (hδ ▸ h0)
    have key := GlobalTheory.FieldProj.interNum_pull_eq_mul (ZMod l) (clo y) (clo (π y)) (strHom (ZMod l) (clo (π y))) g
      (hgs ▸ hWp) hZp U _ hgU hU hU' ⟨hfree, hfin, hrank⟩ d hZd.le (fun _ => L.B.pull (cloι (π y))) (fun _ => hB)
    rw [hδ] at key
    rw [topSelf_def, topSelf_def]
    convert key using 3
    · exact algebra_zmod_eq _ _
    · exact algebra_zmod_eq _ _

end GlobalTheory.ProjFormulaVert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleTranslationInvariantFirstFacto
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPic

namespace GlobalTheory.TranslFst

theorem iso_transl_fst : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : LB (G2 A).left), L.IsLB → (∃ t : (L.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ h : 𝟙_ (Over S) ⟶ A, (∃ t : (L.pull (lift (toUnit A ≫ h) (𝟙 A)).left).Gen, t.IsGen) → LBIso L (L.pull (GlobalTheory.UPel.HT.Hecke.transl (lift h 1 : 𝟙_ (Over S) ⟶ G2 A)).left) := by
  intro S A _ _ hA L hL h1 h2 h hh
  have hG : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have z : ∀ (f : A ⟶ G2 A), (∃ t : (L.pull f.left).Gen, t.IsGen) → pull f.left (cls L hL) = 0 := by
    intro f hf
    rw [← cls_pull hL _ (pull_isLB hL _)]
    exact (cls_eq_zero_iff _).2 hf
  have fac : ∀ (g : G2 A ⟶ A) (e : A ⟶ G2 A), pull e.left (cls L hL) = 0 → pull (g ≫ e).left (cls L hL) = 0 := by
    intro g e he
    rw [Over.comp_left, pull_comp, he, map_zero]
  have cube := GlobalTheory.CubeTop.cubeTheorem S (G2 A) hG L hL (G2 A) (lift (fst A A) 1) (toUnit _ ≫ lift h 1)
    (lift 1 (snd A A))
  have e := (cls_linComb hL _ _ (LB.isLB_linComb hL _ _)).symm.trans ((cls_eq_zero_iff _).2 cube)
  have habc : (lift (fst A A) 1 : G2 A ⟶ G2 A) * (toUnit _ ≫ lift h 1) * lift 1 (snd A A) =
      GlobalTheory.UPel.HT.Hecke.transl (lift h 1 : 𝟙_ (Over S) ⟶ G2 A) := by
    ext <;> simp [GlobalTheory.UPel.HT.Hecke.transl, MonObj.mul_comp, MonObj.comp_mul]
  have hac : (lift (fst A A) 1 : G2 A ⟶ G2 A) * lift 1 (snd A A) = 𝟙 _ := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have hbc : (toUnit _ ≫ lift h 1 : G2 A ⟶ G2 A) * lift 1 (snd A A) = snd A A ≫ lift (toUnit A ≫ h) (𝟙 A) := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have hab : (lift (fst A A) 1 : G2 A ⟶ G2 A) * (toUnit _ ≫ lift h 1) = (fst A A * (toUnit _ ≫ h)) ≫ lift (𝟙 A) 1 := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have ha : (lift (fst A A) 1 : G2 A ⟶ G2 A) = fst A A ≫ lift (𝟙 A) 1 := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have hb : (toUnit _ ≫ lift h 1 : G2 A ⟶ G2 A) = (toUnit _ ≫ h) ≫ lift (𝟙 A) 1 := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have hc : (lift 1 (snd A A) : G2 A ⟶ G2 A) = snd A A ≫ lift 1 (𝟙 A) := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have h1' : (1 : G2 A ⟶ G2 A) = (1 : G2 A ⟶ A) ≫ lift (𝟙 A) 1 := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  simp only [Fin.sum_univ_eight, Matrix.cons_val] at e
  rw [habc, hac, hbc, hab, ha, hb, hc, h1', Over.id_left, pull_id] at e
  simp only [fun g => fac g _ (z _ h1), fun g => fac g _ (z _ h2), fun g => fac g _ (z _ hh)] at e
  have key : pull (GlobalTheory.UPel.HT.Hecke.transl (lift h 1 : 𝟙_ (Over S) ⟶ G2 A)).left (cls L hL) = cls L hL := by
    simp only [one_smul, neg_smul, smul_zero, neg_zero, add_zero, zero_add] at e
    exact eq_of_sub_eq_zero ((sub_eq_add_neg _ _).trans e)
  refine (cls_eq_iff hL (pull_isLB hL _)).1 ?_
  rw [cls_pull hL, key]

end GlobalTheory.TranslFst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleTranslationInvariantSecondFact
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TranslInv

theorem translSnd : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB (G2 A).left), L.IsLB → (∃ t : (L.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ h : 𝟙_ (Over S) ⟶ A,
    (∃ t : (L.pull (lift (𝟙 A) (toUnit A ≫ h)).left).Gen, t.IsGen) →
    LBIso L (L.pull (GlobalTheory.UPel.HT.Hecke.transl (lift 1 h : 𝟙_ (Over S) ⟶ G2 A)).left) := by
  intro S A _ _ hA L hL h0 h1 h hh
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have cube := GlobalTheory.CubeTop.cubeTheorem S (G2 A) hAA L hL (G2 A) (lift (1 : G2 A ⟶ A) (snd A A))
    (toUnit _ ≫ lift 1 h) (lift (fst A A) 1)
  have zero_of : ∀ {Y : Scheme.{0}} (ψ : Y ⟶ (G2 A).left), (∃ t : (L.pull ψ).Gen, t.IsGen) →
      GlobalTheory.CechPic.pull ψ (GlobalTheory.CechPic.cls L hL) = 0 := fun ψ hψ =>
    (GlobalTheory.CechPic.cls_pull hL ψ (pull_isLB hL ψ)).symm.trans ((GlobalTheory.CechPic.cls_eq_zero_iff _).2 hψ)
  have e_abc : lift (1 : G2 A ⟶ A) (snd A A) * (toUnit _ ≫ lift 1 h) * lift (fst A A) 1 =
      GlobalTheory.UPel.HT.Hecke.transl (lift 1 h : 𝟙_ (Over S) ⟶ G2 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [GlobalTheory.UPel.HT.Hecke.transl, MonObj.mul_comp, MonObj.comp_mul]
  have e_ab : lift (1 : G2 A ⟶ A) (snd A A) * (toUnit _ ≫ lift 1 h) =
      (snd A A * (toUnit _ ≫ h)) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have e_ac : lift (1 : G2 A ⟶ A) (snd A A) * lift (fst A A) 1 = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have e_bc : (toUnit _ ≫ lift 1 h) * lift (fst A A) 1 = fst A A ≫ lift (𝟙 A) (toUnit A ≫ h) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have e_a : lift (1 : G2 A ⟶ A) (snd A A) = snd A A ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e_b : (toUnit _ ≫ lift 1 h : G2 A ⟶ G2 A) = (toUnit _ ≫ h) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e_c : lift (fst A A) (1 : G2 A ⟶ A) = fst A A ≫ lift (𝟙 A) (1 : A ⟶ A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e_1 : (1 : G2 A ⟶ G2 A) = (1 : G2 A ⟶ A) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  obtain ⟨t, ht⟩ := cube
  have hz := (GlobalTheory.CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨t, ht⟩
  rw [GlobalTheory.CechPic.cls_linComb hL] at hz
  simp only [Fin.sum_univ_eight, Matrix.cons_val] at hz
  rw [e_abc, e_ab, e_ac, e_bc, e_a, e_b, e_c, e_1] at hz
  simp only [Over.comp_left, Over.id_left, GlobalTheory.CechPic.pull_comp, GlobalTheory.CechPic.pull_id,
    zero_of _ h0, zero_of _ h1, zero_of _ hh, map_zero] at hz
  simp only [one_zsmul, neg_one_zsmul, neg_zero, add_zero, ← sub_eq_add_neg, sub_eq_zero] at hz
  exact (GlobalTheory.CechPic.cls_eq_iff hL (pull_isLB hL _)).1
    ((GlobalTheory.CechPic.cls_pull hL _ (pull_isLB hL _)).trans hz).symm

end GlobalTheory.TranslInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedSectionOfFrameCarriedAlongLifts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem gs_sub' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by simp only [gs_eq f y U h, map_sub]

theorem gs_comp_map {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (V : X.Opens) (hz : h (g z) ∈ V)
    (a : Γ(X, V)) : gs (g ≫ h) z V a = (g.stalkMap z).hom (gs h (g z) V a) := by
  rw [← gs_pull g h z V hz a, gs_eq_map_gs g z (h ⁻¹ᵁ V) hz, gs_pull (𝟙 Y) h (g z) V hz a, Category.id_comp]

theorem secCarriedOver_of_lift {X Z P : Scheme.{0}} (q : Z ⟶ X) (p₁ : Z ⟶ P) (L : LB X) (W O : X.Opens) (hOW : O ≤ W)
    (τ : ∀ k : L.ι, Γ(Z, q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k)ˣ) (d : ℕ) (B : Fin d → Γ(P, ⊤))
    (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k))
    (hdec : ∀ (z : Z) (k : L.ι), q z ∈ O → q z ∈ L.U k →
      gs (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs p₁ z ⊤ (B l) * gs q z (O ⊓ L.U k) (s l k))
    (huniq : ∀ (U : X.Opens) (a : Fin d → Γ(X, U)) (x : X), x ∈ U →
      (∀ z : Z, q z = x → ∑ l, gs p₁ z ⊤ (B l) * gs q z U (a l) = 0) → ∀ l, gs (𝟙 X) x U (a l) = 0)
    (φ : X ⟶ X) (w : LB.Iso L (L.pull φ)) (f' : Z ⟶ Z) (hf'q : f' ≫ q = q ≫ φ) (hf'p : f' ≫ p₁ = p₁)
    (hcar : FrameCarriedAlong L q (q ⁻¹ᵁ W) τ φ w f') (l : Fin d) : SecCarriedOver L O (s l) φ w := by
  have hpt : ∀ z, q (f' z) = φ (q z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hf'q, Scheme.Hom.comp_apply]
  intro x j k hxO hφxO hxk hφxj
  let U' : X.Opens := O ⊓ L.U k ⊓ φ ⁻¹ᵁ (O ⊓ L.U j) ⊓ ((L.pull φ).U (fun _ => j) ⊓ L.U k)
  have h1 : U' ≤ φ ⁻¹ᵁ (O ⊓ L.U j) := fun _ h => h.1.2
  have h2 : U' ≤ (L.pull φ).U (fun _ => j) ⊓ L.U k := fun _ h => h.2
  have h3 : U' ≤ O ⊓ L.U k := fun _ h => h.1.1
  let a : Fin d → Γ(X, U') := fun l' =>
    (X.presheaf.map (homOfLE h1).op).hom ((φ.app (O ⊓ L.U j)).hom (s l' j)) -
      (X.presheaf.map (homOfLE h2).op).hom (w.s (fun _ => j, k)).val * (X.presheaf.map (homOfLE h3).op).hom (s l' k)
  have ha : ∀ {Y : Scheme.{0}} (g : Y ⟶ X) (y : Y) (hy : g y ∈ U') (l' : Fin d),
      gs g y U' (a l') = gs (g ≫ φ) y (O ⊓ L.U j) (s l' j) -
        (gm g y ((L.pull φ).U (fun _ => j) ⊓ L.U k) (w.s (fun _ => j, k))).val * gs g y (O ⊓ L.U k) (s l' k) := by
    intro Y g y hy l'
    have e1 : gs g y U' ((X.presheaf.map (homOfLE h1).op).hom ((φ.app (O ⊓ L.U j)).hom (s l' j))) =
        gs (g ≫ φ) y (O ⊓ L.U j) (s l' j) :=
      (gs_res g y h1 hy _).trans (gs_pull g φ y (O ⊓ L.U j) (h1 hy) _)
    have e2 : gs g y U' ((X.presheaf.map (homOfLE h2).op).hom (w.s (fun _ => j, k)).val) =
        (gm g y ((L.pull φ).U (fun _ => j) ⊓ L.U k) (w.s (fun _ => j, k))).val :=
      (gs_res g y h2 hy _).trans (gs_unit g y _ (h2 hy) _)
    have e3 : gs g y U' ((X.presheaf.map (homOfLE h3).op).hom (s l' k)) = gs g y (O ⊓ L.U k) (s l' k) :=
      gs_res g y h3 hy _
    rw [gs_sub' g y U' hy, gs_mul g y U' hy, e1, e2, e3]
  have hxU : x ∈ U' := ⟨⟨⟨hxO, hxk⟩, hφxO, hφxj⟩, mem_pull.2 hφxj, hxk⟩
  have key := huniq U' a x hxU (by
    intro z hz
    have hzU : q z ∈ U' := hz ▸ hxU
    have hzO : q z ∈ O := hz ▸ hxO
    have hzk : q z ∈ L.U k := hz ▸ hxk
    have hzW : z ∈ q ⁻¹ᵁ W := hOW hzO
    have hf'zO : q (f' z) ∈ O := by rw [hpt, hz]; exact hφxO
    have hf'zj : q (f' z) ∈ L.U j := by rw [hpt, hz]; exact hφxj
    have hmj : q (f' z) ∈ O ⊓ L.U j := ⟨hf'zO, hf'zj⟩
    have hmWj : f' z ∈ q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U j := ⟨hOW hf'zO, hf'zj⟩
    have hmWk : (𝟙 Z) z ∈ q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k := ⟨hzW, hzk⟩
    have hcz := hcar z j k hzW (hOW hf'zO) hzk hf'zj
    have S1 : ∑ l', gs p₁ z ⊤ (B l') * gs (q ≫ φ) z (O ⊓ L.U j) (s l' j) =
        (gm f' z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U j) (τ j)).val := by
      have e1 : ∀ l', gs p₁ z ⊤ (B l') = (f'.stalkMap z).hom (gs p₁ (f' z) ⊤ (B l')) := fun l' => by
        conv_lhs => rw [← hf'p]
        exact gs_comp_map f' p₁ z ⊤ trivial _
      have e2 : ∀ l', gs (q ≫ φ) z (O ⊓ L.U j) (s l' j) = (f'.stalkMap z).hom (gs q (f' z) (O ⊓ L.U j) (s l' j)) :=
        fun l' => by rw [← hf'q]; exact gs_comp_map f' q z _ hmj _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [e1, e2, ← map_mul, ← map_sum]
      rw [← hdec (f' z) j hf'zO hf'zj, ← gs_eq_map_gs f' z _ hmWj, gs_unit f' z _ hmWj]
    have S3 := hdec z k hzO hzk
    rw [gs_unit (𝟙 Z) z _ hmWk] at S3
    have e4 : ∀ l', gs p₁ z ⊤ (B l') * gs q z U' (a l') =
        gs p₁ z ⊤ (B l') * gs (q ≫ φ) z (O ⊓ L.U j) (s l' j) -
          (gw w q z j k).val * (gs p₁ z ⊤ (B l') * gs q z (O ⊓ L.U k) (s l' k)) := fun l' => by
      rw [ha q z hzU l', gw]; ring
    rw [Finset.sum_congr rfl (fun l' _ => e4 l'), Finset.sum_sub_distrib, ← Finset.mul_sum, S1, ← S3, hcz,
      Units.val_mul, sub_self])
  have e := key l
  rw [ha (𝟙 X) x hxU l, Category.id_comp, sub_eq_zero] at e
  exact e

theorem secCarriedOver_of_frameCarriedAlong : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X) (W O : X.Opens), O ≤ W → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ) (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k)), (∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k)) → ∀ (φ : X ⟶ X) (w : LB.Iso L (L.pull φ)), φ ≫ f = f → (∀ f' : (pullback f (spMap ρ₁)) ⟶ (pullback f (spMap ρ₁)), f' ≫ (pullback.fst f (spMap ρ₁)) = (pullback.fst f (spMap ρ₁)) ≫ φ → f' ≫ (pullback.snd f (spMap ρ₁)) = (pullback.snd f (spMap ρ₁)) → FrameCarriedAlong L (pullback.fst f (spMap ρ₁)) ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W) τ φ w f') → ∀ l, SecCarriedOver L O (s l) φ w := by
  intro R R₁ _ _ ρ₁ d b hb X f L W O hOW τ s hdec φ w hφ hcar l
  have hcond : (pullback.fst f (spMap ρ₁) ≫ φ) ≫ f = pullback.snd f (spMap ρ₁) ≫ spMap ρ₁ := by
    rw [Category.assoc, hφ, pullback.condition]
  have hf'q : pullback.lift _ _ hcond ≫ pullback.fst f (spMap ρ₁) = pullback.fst f (spMap ρ₁) ≫ φ :=
    pullback.lift_fst _ _ _
  have hf'p : pullback.lift _ _ hcond ≫ pullback.snd f (spMap ρ₁) = pullback.snd f (spMap ρ₁) :=
    pullback.lift_snd _ _ _
  exact secCarriedOver_of_lift (pullback.fst f (spMap ρ₁)) (pullback.snd f (spMap ρ₁)) L W O hOW τ d
    (fun l => (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) s hdec
    (fun U a x hx hz => _root_.GlobalTheory.Mum.FreeCoord.germ_eq_zero R R₁ ρ₁ d b hb X f U a x hx hz) φ w _ hf'q hf'p (hcar _ hf'q hf'p) l

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTriangularEqEsymmFirstChernForms
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernTri

theorem coeff_charpolyRev_neg_of_tri {R : Type} [CommRing R] {s : ℕ} (F : Matrix (Fin s) (Fin s) R)
    (h : ∀ i j, j < i → F i j = 0) (k : ℕ) :
    (Matrix.charpolyRev (-F)).coeff k = ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, F i i := by
  rw [Matrix.charpolyRev, Matrix.det_of_upperTriangular]
  · have e : ∀ i, ((1 : Matrix (Fin s) (Fin s) (Polynomial R)) -
        (Polynomial.X : Polynomial R) • (-F).map Polynomial.C) i i = 1 + Polynomial.C (F i i) * Polynomial.X := by
      intro i
      rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply, Matrix.map_apply, Matrix.neg_apply, map_neg, smul_eq_mul,
        mul_neg, sub_neg_eq_add, mul_comm]
    simp only [e]
    rw [Finset.prod_one_add, Polynomial.finsetSum_coeff]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod, Polynomial.coeff_C_mul_X_pow]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext t
    simp [eq_comm]
  · intro i j hij
    have hij' : j < i := hij
    simp [h i j hij', hij'.ne']

theorem chernAt_tri : ∀ (n s : ℕ) (T : V n → Matrix (Fin s) (Fin s) ℂ) (d : Fin s → V n → ℝ) (v : V n), MContDiffAt ∞ T v → (∀ i, 0 < d i v) → (∀ᶠ x in 𝓝 v, (∀ i j, i < j → T x i j = 0) ∧ ∀ i, T x i i = d i x) → ∀ j, chernAt T v j = aeval (fun i => ofValues (ddc (fun x => -Real.log (d i x)) v)) (esymm (Fin s) ℂ j) := by
  intro n s T d v hT hd htri j
  have key := _root_.GlobalTheory.ChernCalc.curv_lowerTriangular n s T d v hT hd htri
  rw [chernAt, chernPoly, coeff_charpolyRev_neg_of_tri _ (fun a b hab => by
    simp [curvPoly, fun ξ η => (key ξ η).1 a b hab]), esymm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_prod, aeval_X, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have e (i : Fin s) : ofValues (ddc (fun x => -Real.log (d i x)) v) =
      kappa • (aeval sym (curvPoly T v i i) : Ev n) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ofValues, ddc, curvPoly, Matrix.of_apply, map_sum, map_mul, aeval_C, aeval_X, Finset.smul_sum,
      fun ξ η => (key ξ η).2 i, leviForm_neg, ← Algebra.smul_def, smul_smul, ContinuousLinearMap.neg_apply]
  simp only [e]
  rw [Finset.prod_smul, Finset.prod_const, (Finset.mem_powersetCard.1 ht).2]

end GlobalTheory.ChernTri
end

