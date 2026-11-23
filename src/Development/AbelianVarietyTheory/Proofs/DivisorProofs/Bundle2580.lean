module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Rosati
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubSpFibre
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2492
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompact
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isIntegral_isLocallyNoetherian_compactSpace :
    ∀ (K : Type) [Field K] (A : AbVar K),
      IsIntegral A.X.left ∧ IsLocallyNoetherian A.X.left ∧ CompactSpace A.X.left := by
  intro K _ A
  have hA : IsAbelianScheme A.X := A.ab
  have : Smooth A.X.hom := hA.smooth
  have : IsProper A.X.hom := hA.proper
  have : GeometricallyConnected A.X.hom := hA.geomConnected
  refine ⟨isIntegral_of_smooth_of_geometricallyConnected A.X.hom,
    LocallyOfFiniteType.isLocallyNoetherian A.X.hom, ?_⟩
  exact (quasiCompact_iff_compactSpace A.X.hom).mp inferInstance

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassMulLeft
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem lam_mul_left_of_cube : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left) (Y : Over (Sp K))
    (x x' y : Y ⟶ A.X), AbVar.lam c (x * x') y = AbVar.lam c x y + AbVar.lam c x' y := by
  intro K _ A c Y x x' y
  obtain ⟨L, hL, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  have h := GlobalTheory.CubeTop.cubeTheorem (Sp K) A.X A.ab L hL Y x x' y
  have hl := LB.isLB_linComb hL (fun k : Fin 8 ↦ (![x * x' * y, x * x', x * y, x' * y, x, x', y, 1] k).left)
    ![1, -1, -1, -1, 1, 1, 1, -1]
  have e := (GlobalTheory.CechPic.cls_eq_zero_iff hl).2 h
  rw [GlobalTheory.CechPic.cls_linComb hL _ _ hl, Fin.sum_univ_eight] at e
  simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
  rw [AbVar.lam_eq, AbVar.lam_eq, AbVar.lam_eq]
  simp only [GlobalTheory.CechPic.lam, _root_.mul_one]
  rw [← sub_eq_zero, ← e]
  abel

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassSymmNaturalAdditive
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem lam_symm_nat_add : ∀ (K : Type) [Field K] (A B : AbVar K) (c c' : Pic A.X.left) (d : Pic B.X.left) (f : A ⟶ B) (Y Z : Over (Sp K)) (u : Z ⟶ Y) (x y : Y ⟶ A.X), AbVar.lam c x y = AbVar.lam c y x ∧ CechPic.pull u.left (AbVar.lam c x y) = AbVar.lam c (u ≫ x) (u ≫ y) ∧ AbVar.lam d (x ≫ f.hom) (y ≫ f.hom) = AbVar.lam (CechPic.pull f.hom.left d) x y ∧ AbVar.lam (c + c') x y = AbVar.lam c x y + AbVar.lam c' x y := by
  intro K _ A B c c' d f Y Z u x y
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [AbVar.lam_eq, AbVar.lam_eq]; exact CechPic.lam_comm c x y
  · rw [AbVar.lam_eq, AbVar.lam_eq]; exact CechPic.pull_lam u c x y
  · rw [AbVar.lam_eq, AbVar.lam_eq]; exact (CechPic.lam_pull f.hom d x y).symm
  · simp only [AbVar.lam, map_add (f := _)]; abel

end GlobalTheory.AV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveOfTrivAxes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubeAxes

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem lift_mul_lift {Y : Over S} (a a' b b' : Y ⟶ G) : lift a b * lift a' b' = lift (a * a') (b * b') := by
  ext <;> simp [MonObj.mul_comp]

theorem cube_cls (hG : IsAbelianScheme G) {P : LB (G ⊗ G).left} (hP : P.IsLB) {Y : Over S} (a b c : Y ⟶ G ⊗ G) :
    CechPic.pull (a * b * c).left (cls P hP) - CechPic.pull (a * b).left (cls P hP) - CechPic.pull (a * c).left (cls P hP)
      - CechPic.pull (b * c).left (cls P hP) + CechPic.pull a.left (cls P hP) + CechPic.pull b.left (cls P hP)
      + CechPic.pull c.left (cls P hP) - CechPic.pull (1 : Y ⟶ G ⊗ G).left (cls P hP) = 0 := by
  have hGG := AbelianSchemeGerms.isAbelianScheme_tensor G G hG hG
  have T := GlobalTheory.CubeTop.cubeTheorem S (G ⊗ G) hGG P hP Y a b c
  have z := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 T
  rw [cls_linComb hP] at z
  simp only [Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at z
  rw [← z]
  abel

theorem additive_of_triv_axes : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G], IsAbelianScheme G →
    ∀ {P : LB (G ⊗ G).left} (hP : P.IsLB), (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → IsAdditive P ∧ IsAdditive (swap P) := by
  intro S G _ hG P hP h₁ h₂
  have l : ∀ {Y : Over S} (a : Y ⟶ G), evc hP 1 a = 0 := fun a ↦ evc_one_left hP h₁ a
  have r : ∀ {Y : Over S} (a : Y ⟶ G), evc hP a 1 = 0 := fun a ↦ evc_one_right hP h₂ a
  have o : ∀ {Y : Over S}, (1 : Y ⟶ G ⊗ G) = lift 1 1 := by
    intro Y
    ext <;> simp
  refine ⟨(isAdditive_iff hP).2 fun Y x x' y ↦ ?_, (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).2 fun Y x y y' ↦ ?_⟩
  · have e := cube_cls hG hP (lift x 1) (lift x' 1) (lift 1 y)
    simp only [lift_mul_lift, _root_.mul_one, _root_.one_mul, o] at e
    change evc hP (x * x') y - evc hP (x * x') 1 - evc hP x y - evc hP x' y + evc hP x 1 + evc hP x' 1
      + evc hP 1 y - evc hP 1 1 = 0 at e
    rw [r, r, r, r, l] at e
    rw [← sub_eq_zero, ← e]
    abel
  · have e := cube_cls hG hP (lift 1 y) (lift 1 y') (lift x 1)
    simp only [lift_mul_lift, _root_.mul_one, _root_.one_mul, o] at e
    change evc hP x (y * y') - evc hP 1 (y * y') - evc hP x y - evc hP x y' + evc hP 1 y + evc hP 1 y'
      + evc hP x 1 - evc hP 1 1 = 0 at e
    rw [l, l, l, l, r] at e
    rw [← sub_eq_zero, ← e]
    abel

end GlobalTheory.CubeAxes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleCubicalLineBundle
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SS.AbAmple

open GlobalTheory.CechPic GlobalTheory.TripleExt

theorem cubeCls_eq_zero {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (c : Pic A.left) : cubeCls (x3 A) c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have h := GlobalTheory.CubeTop.cubeTheorem S A hA L hL (G3 A) (x3 A 0) (x3 A 1) (x3 A 2)
  have h₀ := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 h
  rw [cls_linComb hL, Fin.sum_univ_eight] at h₀
  have e : x3 A = ![x3 A 0, x3 A 1, x3 A 2] := by
    funext i; fin_cases i <;> rfl
  rw [e, GlobalTheory.SS.AmpCub.cubeCls_three]
  rw [← h₀]
  simp
  abel

end GlobalTheory.SS.AbAmple

namespace GlobalTheory.SS

open GlobalTheory.CechPic AbAmple

theorem exists_ampleCub_of_isAbelianScheme :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B →
      ∃ L : LB B.left, GlobalTheory.SS.AmpleCub B L := by
  intro k _ _ B _ hB
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom := geometricallyIntegral_of_smooth _
  have : IsIntegral B.left :=
    GeometricallyIntegral.geometrically_isIntegral (f := B.hom) (𝟙 _) _ _ (IsPullback.id_horiz B.hom)
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : B.left.IsSeparated := ⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩
  have hst : ∀ x : B.left, UniqueFactorizationMonoid (B.left.presheaf.stalk x) := fun x =>
    have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth k B.hom x
    uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      isPrincipal_map_away_of_hasProjectiveDimensionLE _
  obtain ⟨y⟩ : Nonempty B.left := inferInstance
  obtain ⟨W, hW, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  obtain ⟨L, s, hL, hs⟩ := exists_nonzeroLocus_eq_of_isAffineOpen B.left hst W hW ⟨y, hy⟩
  exact AmpCub.exists_ampleCub (cubeCls_eq_zero B hB (cls L hL)) ⟨L, hL, s, rfl, hs⟩ hW ⟨y, hy⟩

end GlobalTheory.SS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanIntegralPullMulDegree
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
open MeasureTheory GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchPull

open Set

theorem setIntegral_pull {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {p : X ⟶ Sp k} {e : ℕ} (hX : IsArithVar p e) (g : Y ⟶ X) (hY : IsArithVar (g ≫ p) e)
    (hη : g (genericPoint Y) = genericPoint X) (hδ : g.residueDegree (genericPoint Y) ≠ 0)
    (N : HermLB p) (σ : k →+* ℂ) (U : X.Opens) (hU : genericPoint X ∈ U)
    (f : CxPts p σ → ℝ) (hf : ContinuousOn f (ptsIn p σ U))
    (S' : Set (CxPts (g ≫ p) σ)) (hsub : ptsIn (g ≫ p) σ (g ⁻¹ᵁ U) ⊆ S')
    (f' : CxPts (g ≫ p) σ → ℝ)
    (hf' : EqOn f' (fun y => f (PtsOver.map g rfl _ y)) (ptsIn (g ≫ p) σ (g ⁻¹ᵁ U)))
    (ε : ℤˣ) :
    ∫ y in S', f' y ∂((N.restr g).φ σ).chernPart e ε =
      (g.residueDegree (genericPoint Y) : ℝ) * ∫ x in ptsIn p σ U, f x ∂(N.φ σ).chernPart e ε := by
  obtain ⟨V, hVη, hV⟩ := GlobalTheory.CoverDeg.exists_open_covering_charts hX hY g rfl hη hδ
  obtain ⟨hcard, hchart, hlift⟩ := hV σ
  set F := PtsOver.map g (rfl : g ≫ p = g ≫ p) (spMap σ) with hFdef
  have hFm : Measurable F := (PtsOver.continuous_map _ _ _).measurable
  have hpre : ∀ W : X.Opens, F ⁻¹' ptsIn p σ W = ptsIn (g ≫ p) σ (g ⁻¹ᵁ W) := by
    intro W
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have hUm : MeasurableSet (ptsIn p σ U) := (isOpen_ptsIn U).measurableSet
  have hVm : MeasurableSet (ptsIn p σ V) := (isOpen_ptsIn V).measurableSet
  have h0 : (N.φ σ).chernPart e ε (ptsIn p σ V)ᶜ = 0 := by
    have h := GlobalTheory.ChernNull.chernPart_over_closed hX ((V : X.Opens) : Set X)ᶜ
      V.isOpen.isClosed_compl (by simp [hVη]) σ (N.φ σ) ε
    convert h using 2
    ext y
    simp [mem_ptsIn]
  have hmeas : (g.residueDegree (genericPoint Y) : ℝ≥0∞) •
      ((N.φ σ).chernPart e ε).restrict (ptsIn p σ U) =
      Measure.map F ((((N.φ σ).pull g rfl).chernPart e ε).restrict
        (F ⁻¹' (ptsIn p σ U ∩ ptsIn p σ V))) := by
    ext A hA
    rw [Measure.smul_apply, Measure.restrict_apply hA, Measure.map_apply hFm hA,
      Measure.restrict_apply (hFm hA), ← Set.preimage_inter,
      GlobalTheory.CoverChern.chernPart_preimage_of_cover hX hY g rfl (N.φ σ) (N.cInf σ) ε (ptsIn p σ V)
        (isOpen_ptsIn V) _ hcard hchart hlift
        (fun c c' hc w hw => GlobalTheory.PullChartDens.chernDens_pull_of_chart g rfl (N.φ σ) (N.cInf σ)
          c c' hc w hw) _
        (hA.inter (hUm.inter hVm)) (fun x hx => hx.2.2), smul_eq_mul, ← Set.inter_assoc,
      measure_inter_conull h0]
  set T' := F ⁻¹' (ptsIn p σ U ∩ ptsIn p σ V) with hT'
  have hT'eq : T' = ptsIn (g ≫ p) σ (g ⁻¹ᵁ U) ∩ ptsIn (g ≫ p) σ (g ⁻¹ᵁ V) := by
    rw [hT', Set.preimage_inter, hpre, hpre]
  have hT'm : MeasurableSet T' := hFm (hUm.inter hVm)
  have hT'U : T' ⊆ ptsIn (g ≫ p) σ (g ⁻¹ᵁ U) := by
    rw [hT'eq]; exact Set.inter_subset_left
  have h0' : ((N.φ σ).pull g rfl).chernPart e ε T'ᶜ = 0 := by
    have h := GlobalTheory.ChernNull.chernPart_over_closed hY (g ⁻¹' ((U ⊓ V : X.Opens) : Set X)ᶜ)
      ((U ⊓ V).isOpen.isClosed_compl.preimage g.continuous) (by simp [hη, hU, hVη]) σ
      ((N.φ σ).pull g rfl) ε
    convert h using 2
    rw [hT'eq]
    ext y
    simp [mem_ptsIn]

  have hae : S' =ᵐ[((N.φ σ).pull g rfl).chernPart e ε] T' := by
    refine ae_eq_set.2 ⟨measure_mono_null (fun x hx => hx.2) h0', ?_⟩
    rw [Set.diff_eq_empty.2 (hT'U.trans hsub)]
    exact measure_empty
  have hfm : AEStronglyMeasurable f (Measure.map F ((((N.φ σ).pull g rfl).chernPart e ε).restrict T')) := by
    rw [← hmeas]
    exact (hf.aestronglyMeasurable hUm).smul_measure _
  calc ∫ y in S', f' y ∂((N.restr g).φ σ).chernPart e ε
      = ∫ y in T', f' y ∂((N.φ σ).pull g rfl).chernPart e ε := setIntegral_congr_set hae
    _ = ∫ y in T', f (F y) ∂((N.φ σ).pull g rfl).chernPart e ε :=
        setIntegral_congr_fun hT'm (hf'.mono hT'U)
    _ = ∫ x, f x ∂Measure.map F ((((N.φ σ).pull g rfl).chernPart e ε).restrict T') :=
        (integral_map hFm.aemeasurable hfm).symm
    _ = _ := by
        rw [← hmeas, integral_smul_measure, ENNReal.toReal_natCast, smul_eq_mul]

theorem archInt_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (e : ℕ), IsArithVar p e → IsArithVar q e → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), g.residueDegree (genericPoint Y) ≠ 0 → ∀ (M N : HermLB p) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (N.pull g hg).archInt (M.pull g hg) e (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) = (g.residueDegree (genericPoint Y) : ℝ) * N.archInt M e hr := by
  intro k _ X Y _ _ p q e hX hY g hg hη hδ M N r hr
  subst hg
  have hη' : g (genericPoint Y) ⤳ genericPoint X := hη ▸ specializes_rfl
  have hU : genericPoint X ∈ (M.div hr).supp.compl := (M.div hr).genericPoint_notMem_supp
  have key : ∀ σ : k →+* ℂ,
      ((N.restr g).φ σ).chernInt e
        (offSupp (g ≫ p) σ ((M.restr g).div (MultPull.isRatSec_pull_map g hη' hr)))
        (logNorm ((M.restr g).φ σ) (fun c => Units.map (TrueGeo.SmallSec.fnMap g hη').toMonoidHom
          (r (c PUnit.unit)))) =
      (g.residueDegree (genericPoint Y) : ℝ) *
        (N.φ σ).chernInt e (offSupp p σ (M.div hr)) (logNorm (M.φ σ) r) := by
    intro σ
    have hsub := fun (y : CxPts (g ≫ p) σ) (hy : y ∈ ptsIn (g ≫ p) σ (g ⁻¹ᵁ (M.div hr).supp.compl)) =>
      ArchIntAlter.mem_offSupp_pull M g hη' hr hy
    have hf' := fun (y : CxPts (g ≫ p) σ) (hy : y ∈ ptsIn (g ≫ p) σ (g ⁻¹ᵁ (M.div hr).supp.compl)) =>
      ArchIntAlter.logNorm_pull M g hη' hr hy
    have hc := ArchIntAlter.continuousOn_logNorm (M.φ σ) hr (M.cInf σ)
    unfold Weight.chernInt
    rw [setIntegral_pull hX g hY hη hδ N σ _ hU _ hc _ hsub _ hf' 1,
      setIntegral_pull hX g hY hη hδ N σ _ hU _ hc _ hsub _ hf' (-1), mul_sub]
    rfl
  unfold HermLB.archInt
  refine (finsum_congr key).trans ?_
  exact (mul_finsum _ _).symm

end GlobalTheory.ArchPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryPlaceNotDvdDifferentBaseField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DifferentAtBasePlace

theorem ne_of_mod_eq_one' {p M k : ℕ} (hp : p % M = 1) (hk : k ∣ M) (hk1 : 1 < k) : p ≠ k := by
  rintro rfl
  have h := Nat.mod_mod_of_dvd p hk
  rw [hp, Nat.mod_self, Nat.mod_eq_of_lt hk1] at h
  exact one_ne_zero h

theorem natAbs_discr_F_dvd (D : D7) : (discr D.host.F).natAbs ∣ (discr D.host.E).natAbs := by
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow D.host.F (𝓞 D.host.F) D.host.E (𝓞 D.host.E)]
  exact Dvd.dvd.mul_left (dvd_pow_self _ Module.finrank_pos.ne') _

theorem leastSplitAuxiliaryPrime_not_dvd_discr_base (D : D7) : ¬ q0 D ∣ (discr D.host.F).natAbs := by
  obtain ⟨hp, hm, -⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
  intro h
  have hc : q0 D ∣ Formalism.BasicNotions.LevelStarExponents.condE D :=
    D.host.der.discr_primes.1 _ hp (Int.natCast_dvd.2 (h.trans (natAbs_discr_F_dvd D)))
  exact ne_of_mod_eq_one' hm (dvd_mul_of_dvd_right hc _) hp.one_lt rfl

theorem not_dvd_different {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) :
    ¬ G.pl.v0.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  intro h
  have hdisc : ((discr D.host.F : ℤ) : 𝓞 D.host.F) ∈ G.pl.v0.asIdeal :=
    Ideal.le_of_dvd h (discr_mem_differentIdeal D.host.F (𝓞 D.host.F))
  have hq : ((q0 D : ℕ) : 𝓞 D.host.F) ∈ G.pl.v0.asIdeal := G.pl.basePlace_over_qZero
  have hcop : IsCoprime (q0 D : ℤ) (discr D.host.F) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm, Int.gcd, Int.natAbs_natCast]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (leastSplitAuxiliaryPrimeThetaChain_spec D).1).2 (leastSplitAuxiliaryPrime_not_dvd_discr_base D))
  obtain ⟨u, v, huv⟩ := hcop
  apply G.pl.v0.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have := congrArg (Int.cast : ℤ → 𝓞 D.host.F) huv
  push_cast at this
  rw [← this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (by exact_mod_cast hq)) (Ideal.mul_mem_left _ _ hdisc)

end GlobalTheory.DifferentAtBasePlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiadditiveClassEqPoincarePullbackUniqueHom
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.FamHom

theorem main : ∀ (K : Type) [Field K] (A A' T : AbVar K) (P : LB (A.X ⊗ A'.X).left) (hP : AbDual.IsDual A.X A'.X P)
    (β : Pic (A.X ⊗ T.X).left), (∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ T.X),
      CechPic.pull (lift (a * a') t).left β = CechPic.pull (lift a t).left β + CechPic.pull (lift a' t).left β) →
    CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ T.X)).left β = 0 →
    ∃! ψ : T ⟶ A', β = AbDual.evc hP.isLB (fst A.X T.X) (snd A.X T.X ≫ ψ.hom) := by
  intro K _ A A' T P hP β hadd h0
  obtain ⟨M, hM, rfl⟩ := cls_surj β
  have hMa : AbDual.IsAdditive M := (AbDual.isAdditive_iff hM).2 fun Y a a' t => hadd Y a a' t
  obtain ⟨x, hx, hu⟩ := hP.univ T.X M hM hMa
  have hE : (AbDual.ev P (fst A.X T.X) (snd A.X T.X ≫ x)).IsLB := pull_isLB hP.isLB _
  have c : cls M hM = AbDual.evc hP.isLB (fst A.X T.X) (snd A.X T.X ≫ x) := (cls_eq_iff hM hE).2 hx
  have Kx : ∀ (Y : Over (Sp K)) (a : Y ⟶ A.X) (t : Y ⟶ T.X),
      AbDual.evc hP.isLB a (t ≫ x) = AbDual.evc hM a t := by
    intro Y a t
    have k := AbDual.evc_ev hP.isLB (fst A.X T.X) (snd A.X T.X ≫ x) hE a t
    rw [lift_fst, lift_snd_assoc] at k
    rw [← k]
    unfold AbDual.evc
    rw [c]
    rfl
  have h1 := (AbDual.triv_ev_iff hM (𝟙 A.X) (1 : A.X ⟶ T.X)).2 h0
  have u : snd A.X (𝟙_ (Over (Sp K))) ≫ (η[T.X] : 𝟙_ (Over (Sp K)) ⟶ T.X) = 1 := by
    show _ = toUnit _ ≫ η
    rw [toUnit_unique (snd A.X (𝟙_ (Over (Sp K)))) (toUnit _)]
  have e1 : η[T.X] ≫ x = 1 := by
    apply hP.eq_one
    rw [AbDual.triv_ev_iff hP.isLB, ← Category.assoc, Kx, u, AbDual.evc_one_right hM h1]
  have hpt : η[T.X] ≫ x = η[A'.X] := by
    rw [e1]
    show toUnit _ ≫ η = η
    rw [toUnit_unique (toUnit (𝟙_ (Over (Sp K)))) (𝟙 _), Category.id_comp]
  have hmon : IsMonHom x := rigidity_holds (Sp K) T.X A'.X T.ab A'.ab x hpt
  refine ⟨Hom.mk x, c, fun ψ hψ => ?_⟩
  have hE' : (AbDual.ev P (fst A.X T.X) (snd A.X T.X ≫ ψ.hom)).IsLB := pull_isLB hP.isLB _
  have hψ' : LBIso M (AbDual.ev P (fst A.X T.X) (snd A.X T.X ≫ ψ.hom)) := (cls_eq_iff hM hE').1 hψ
  exact Subtype.ext (hu ψ.hom hψ')

end GlobalTheory.AV.FamHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersEighthPowerElementaryMatricesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characters_eighthPower_elementaryMatrices_alt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → (Function.Bijective fun y : Fin 8 → D.toPre.X => ∑ v, c v (y v)) ∧ ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr a b f₁ → (Over.pullback (jK R)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ w x, m (c w x) = if w = a then c b x else 0 := by
  first | exact @GlobalTheory.Poinc.Eq8.characters_eighthPower_elementaryMatrices | exact GlobalTheory.Poinc.Eq8.characters_eighthPower_elementaryMatrices | (intros; apply GlobalTheory.Poinc.Eq8.characters_eighthPower_elementaryMatrices <;> assumption)
end

