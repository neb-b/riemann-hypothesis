module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFormsVanishingComplexPointsFullJets
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AffineGermSubalgebraSmooth
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_germ_subalgebra_smooth : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [Smooth p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (U : Z.Opens), IsAffineOpen U → ∀ (h : genericPoint Z ∈ U) (B : Subalgebra ℂ Z.functionField), (∀ y, y ∈ B ↔ ∃ f : Γ(Z, U), (Z.presheaf.germ U (genericPoint Z) h).hom f = y) → Algebra.Smooth ℂ B := by
  first | (exact @GlobalTheory.germImage_smooth) | (exact GlobalTheory.germImage_smooth) | (intros; apply GlobalTheory.germImage_smooth  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicIndependentPulledBackProjCoordinateRatiStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicIndependent_pulledBackProjCoordinateRatios : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → AlgebraicIndependent ℂ (fun j : Fin d => rat φ 0 j.succ) := by
  first | (exact @GlobalTheory.PD.XCover.algebraicIndependent_rat) | (exact GlobalTheory.PD.XCover.algebraicIndependent_rat) | (intros; apply GlobalTheory.PD.XCover.algebraicIndependent_rat  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicSardShiftedFunctionsRegularZeros
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

set_option autoImplicit false
noncomputable section
open TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CxPts

namespace GlobalTheory.AlgSard

variable {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {d : ℕ}

theorem countable_charts [SmoothOfRelativeDimension d p] {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ C : Set (AlgChart p (RingHom.id ℂ) d), C.Countable ∧
      ∀ z ∈ ptsIn p (RingHom.id ℂ) U, ∃ ch ∈ C, z ∈ ch.e.source := by
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  have h1 := Scheme.Hom.finiteType_appLE p (isAffineOpen_top (Sp ℂ)) hU (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective
  have hft : (algX p U).FiniteType := h1.comp h2
  obtain ⟨k, G, ⟨hom⟩⟩ := GlobalTheory.AffCxPts.homeomorph_zeroSet X p U hU hft
  haveI : SecondCountableTopology (ptsIn p (RingHom.id ℂ) U) := hom.secondCountableTopology
  choose ch hch using fun y : ptsIn p (RingHom.id ℂ) U =>
    AlgChart.exists_mem_source (p := p) (D := d) (σ := RingHom.id ℂ) y.1
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun y : ptsIn p (RingHom.id ℂ) U =>
      (Subtype.val ⁻¹' (ch y).e.source : Set (ptsIn p (RingHom.id ℂ) U)))
    (fun y => (ch y).e.open_source.preimage continuous_subtype_val)
  refine ⟨ch '' T, hT.image _, fun z hz => ?_⟩
  have hm : (⟨z, hz⟩ : ptsIn p (RingHom.id ℂ) U) ∈ ⋃ i ∈ T, Subtype.val ⁻¹' (ch i).e.source := by
    rw [hTU]; exact mem_iUnion.2 ⟨⟨z, hz⟩, hch _⟩
  obtain ⟨y, hyT, hy⟩ := mem_iUnion₂.1 hm
  exact ⟨ch y, mem_image_of_mem _ hyT, hy⟩

end GlobalTheory.AlgSard


open GlobalTheory.AlgSard in
theorem GlobalTheory.AlgSard.main : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (U : X.Opens), IsAffineOpen U →
    ∀ φ : Fin d → Γ(X, U), ∃ E : Set (Fin d → ℂ), MeasureTheory.volume E = 0 ∧
      ∀ c ∉ E, ∀ (z : CxPts p (RingHom.id ℂ)) (hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
        (∀ j, CxPts.evHom hz (φ j) + c j = 0) →
        RingHom.ker (CxPts.evHom hz) ≤
          Ideal.span (Set.range fun j => φ j + ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U (c j)) ⊔ RingHom.ker (CxPts.evHom hz) ^ 2 := by
  intro X p d _ U hU φ
  obtain ⟨C, hC, hcov⟩ := countable_charts (p := p) (d := d) hU
  choose E hE0 hE using fun ch : AlgChart p (RingHom.id ℂ) d => GlobalTheory.T.null_negEval_of_jacobian_det_eq_zero X p d U ch φ
  refine ⟨⋃ ch ∈ C, E ch, (measure_biUnion_null_iff hC).2 fun ch _ => hE0 ch, ?_⟩
  intro c hc z hz hzero
  obtain ⟨ch, hchC, hzc⟩ := hcov z hz
  have hcz : c = fun j => -evHom hz (φ j) := funext fun j => by linear_combination hzero j
  have hdet : (ch.jacMat φ z).det ≠ 0 := fun h0 =>
    hc (mem_biUnion hchC (hcz ▸ hE ch z hzc hz h0))
  have key := GlobalTheory.T.ker_evalComplexPoint_le_span_jacobian X p d U hU ch φ z hzc hz hdet
  have e : (fun j => φ j + algX p U (c j)) = fun j => φ j - algX p U (evHom hz (φ j)) := by
    funext j; rw [hcz, map_neg, sub_eq_add_neg]
  rw [e]; exact key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechComparisonDegreeZeroAlternatingPullback
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull

namespace GlobalTheory

theorem cechAbPull_degZero : ∀ {T T' : TopCat.{0}} (f : T' ⟶ T) {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
    [Finite ι] [Finite κ] {V : Opens T} {U : ι → Opens T} {V' : Opens T'} {U' : κ → Opens T'}
    (τ : κ → ι) (hτ : ∀ s : Finset κ, cechOpen V' U' s ≤ (Opens.map f).obj (cechOpen V U (s.image τ)))
    (hc : V ≤ ⨆ i, U i) (hc' : V' ≤ ⨆ k, U' k) (hV : V' ≤ (Opens.map f).obj V)
    {F : AbSheaf T} {G : AbSheaf T'} (φ : F ⟶ (push f).obj G) (hF : CechAcyclic V U F)
    (hG : CechAcyclic V' U' G) (x : LinearMap.ker (Cube.d (cechAbCube F.obj V U) (0 + 1)))
    (y : LinearMap.ker (Cube.d (cechAbCube G.obj V' U') (0 + 1))),
    y.1 = (cechAbPull f τ hτ φ).term (0 + 1) x.1 →
    cechAbHEquivH' hc' hG 0 (cechClass _ 0 y) =
      SheafPull.pull f φ 0 (homOfLE hV) (cechAbHEquivH' hc hF 0 (cechClass _ 0 x)) := by
  intro T T' f ι κ _ _ _ _ V U V' U' τ hτ hc hc' hV F G φ hF hG x y hy
  obtain ⟨s, hs⟩ := (cechAbHZeroEquiv F.property hc).symm.surjective (cechClass _ 0 x)
  rw [cechAbHZeroEquiv_symm_apply] at hs
  have h1 : cechClass (cechAbCube F.obj V U) 0
      ⟨presheafCechAug (F.obj ⋙ abToIntModule) V U s,
        LinearMap.mem_ker.2 (d_presheafCechAug (F.obj ⋙ abToIntModule) V U s)⟩ =
      cechClass _ 0 x := (presheafToCechH_apply (F.obj ⋙ abToIntModule) V U s).symm.trans hs
  have hx : x.1 = presheafCechAug (F.obj ⋙ abToIntModule) V U s :=
    (congrArg Subtype.val ((cechClass_zero_bijective _).1 h1)).symm
  obtain ⟨s'', hs''⟩ : ∃ s'', s'' = G.obj.map (homOfLE hV).op (φ.hom.app (op V) s) := ⟨_, rfl⟩
  have hy' : y.1 = presheafCechAug (G.obj ⋙ abToIntModule) V' U' s'' := by
    funext t
    obtain ⟨t, ht⟩ := t
    obtain ⟨k, rfl⟩ := Finset.card_eq_one.1 ht
    rw [hy, Cube.PullHom.term_apply_of_injOn _ _ _ (by simp)]
    have hsg : PD.sortSign τ {k} = 1 := by simp [PD.sortSign]
    rw [hsg, one_smul]
    show G.obj.map (homOfLE (hτ {k})).op (φ.hom.app (op (cechOpen V U (({k} : Finset κ).image τ)))
      (x.1 ⟨({k} : Finset κ).image τ, Cube.PullHom.card_image ⟨{k}, ht⟩ (by simp)⟩)) =
      G.obj.map (homOfLE (cechOpen_le V' U' {k})).op s''
    rw [hx, hs'']
    have nat := ConcreteCategory.congr_hom
      (φ.hom.naturality (homOfLE (cechOpen_le V U (({k} : Finset κ).image τ))).op) s
    change φ.hom.app _ (F.obj.map _ s) = G.obj.map _ (φ.hom.app _ s) at nat
    change G.obj.map _ (φ.hom.app _ (F.obj.map (homOfLE (cechOpen_le V U (({k} : Finset κ).image τ))).op s)) = _
    rw [nat]
    refine (ConcreteCategory.congr_hom (G.obj.map_comp _ _) _).symm.trans
      (Eq.trans ?_ (ConcreteCategory.congr_hom (G.obj.map_comp _ _) _))
    rfl
  have h2 : cechClass _ 0 y = toCechAbH G.obj V' U' s'' :=
    (congrArg (cechClass _ 0) (Subtype.ext hy')).trans
      (presheafToCechH_apply (G.obj ⋙ abToIntModule) V' U' s'').symm
  rw [h2, ← hs, cechAbHEquivH'_toCechAbH, cechAbHEquivH'_toCechAbH]
  apply (SheafLES.equivZero G V').injective
  rw [AddEquiv.apply_symm_apply, SheafPull.equivZero_pull, AddEquiv.apply_symm_apply, hs'']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFormsVanishingComplexPointsFullJetsStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_forms_vanishing_complexPoints_fullJets : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (N : ℕ)
    (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι → ι ≫ PSpace.str ℂ N = p → ∀ S : Finset (CxPts p (RingHom.id ℂ)),
    ∃ (n : ℕ) (h : MvPolynomial (Fin (N + 1)) ℂ) (g : Fin d → MvPolynomial (Fin (N + 1)) ℂ)
      (hh : h ∈ GlobalTheory.ProjSpace.grading ℂ N n) (hg : ∀ j, g j ∈ GlobalTheory.ProjSpace.grading ℂ N n), 0 < n ∧
      (∀ j, genericPoint X ∈ GlobalTheory.EtProj.fOpen ι (g j)) ∧
      (∀ y ∈ S, ∀ j, y ∉ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (g j))) ∧
      (∀ z : CxPts p (RingHom.id ℂ), z ∉ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι h) →
        (∀ j, z ∉ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (g j))) → z ∈ S) ∧
      ∀ y ∈ S, ∀ (f₀ : MvPolynomial (Fin (N + 1)) ℂ) (hf₀ : f₀ ∈ GlobalTheory.ProjSpace.grading ℂ N n)
        (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι f₀)),
        GlobalTheory.EtProj.fRatio ι h f₀ hh hf₀ ∈ RingHom.ker (CxPts.evHom hy) ^ 2 ∧
        RingHom.ker (CxPts.evHom hy) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (g j) f₀ (hg j) hf₀) ⊔
          RingHom.ker (CxPts.evHom hy) ^ 2 := by
  first | (exact @GlobalTheory.EtProj.Jets.exists_jet_forms) | (exact GlobalTheory.EtProj.Jets.exists_jet_forms) | (intros; apply GlobalTheory.EtProj.Jets.exists_jet_forms  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteEtaleFunctionFieldIntegralClosureDifferentStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteEtale_functionField_integralClosure_differentials : ∀ (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (c : Y ⟶ Z), c ≫ s = s' → IsFinite c → Etale c → ∀ (d : ℕ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] [i1 : Algebra ℂ Z.functionField] [i2 : Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField], i1 = ffAlg s → i2 = ffAlg s' → (∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : genericPoint Y ∈ c ⁻¹ᵁ U) (f : Γ(Z, U)), (Y.presheaf.germ (c ⁻¹ᵁ U) (genericPoint Y) hU').hom ((c.app U).hom f) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ U (genericPoint Z) hU).hom f)) → FiniteDimensional Z.functionField Y.functionField ∧ ∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : genericPoint Y ∈ c ⁻¹ᵁ U) (B : Subalgebra ℂ Z.functionField) (B' : Subalgebra ℂ Y.functionField), IsAffineOpen U → (∀ y, y ∈ B ↔ ∃ f : Γ(Z, U), (Z.presheaf.germ U (genericPoint Z) hU).hom f = y) → (∀ y, y ∈ B' ↔ ∃ f : Γ(Y, c ⁻¹ᵁ U), (Y.presheaf.germ (c ⁻¹ᵁ U) (genericPoint Y) hU').hom f = y) → (∀ y ∈ B', IsIntegral B (y : Y.functionField)) ∧ (∀ x : Z.functionField, IsIntegral B x → x ∈ B) ∧ (∀ y : Y.functionField, IsIntegral B y → y ∈ B') ∧ (∀ v ∈ B', ∃ (m : ℕ) (b : Fin m → Y.functionField) (w : Fin m → Z.functionField), (∀ j, b j ∈ B' ∧ w j ∈ B) ∧ ι1 (D ℂ Y.functionField v) = ∑ j, b j • mapDR ℂ Z.functionField Y.functionField (ι1 (D ℂ Z.functionField (w j)))) := by
  first | (exact @GlobalTheory.W1.SchFF.finiteEtale_functionField) | (exact GlobalTheory.W1.SchFF.finiteEtale_functionField) | (intros; apply GlobalTheory.W1.SchFF.finiteEtale_functionField  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteProjectionFunctionField
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_projection_function_field : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → FiniteDimensional (fld φ) Z.functionField := by
  first | (exact @GlobalTheory.PD.XCover.finiteDimensional_fld) | (exact GlobalTheory.PD.XCover.finiteDimensional_fld) | (intros; apply GlobalTheory.PD.XCover.finiteDimensional_fld  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermChartInterIntegralCoordinateRatios
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

set_option autoImplicit false
noncomputable section
open MvPolynomial
open scoped GlobalTheory.ProjSpace
namespace GlobalTheory.PD.XCover.Integ
attribute [local instance] MvPolynomial.gradedAlgebra
variable {d : ℕ}

theorem ratioSec_eq_ratio (i j : Fin (d + 1)) : ratioSec d i j = GlobalTheory.ProjSpace.ratio ℂ d i j := by
  rw [ratioSec, GlobalTheory.ProjFrac.awayToSection_mk]
  exact GlobalTheory.ProjFrac.frac_eq (by ring)

theorem basicOpen_ratioSec (a i : Fin (d + 1)) :
    (PSpace ℂ d).basicOpen (ratioSec d a i) = chart d a ⊓ chart d i := by
  rw [ratioSec_eq_ratio]
  exact GlobalTheory.ProjSpace.basicOpen_ratioOn

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem basicOpen_prod (φ : Z ⟶ PSpace ℂ d) (a : Fin (d + 1)) (T : Finset (Fin (d + 1))) :
    Z.basicOpen (φ.app (chart d a) (∏ i ∈ T, ratioSec d a i)) =
      φ ⁻¹ᵁ chart d a ⊓ T.inf fun i => φ ⁻¹ᵁ chart d i := by
  rw [← Scheme.preimage_basicOpen]
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Scheme.basicOpen_of_isUnit _ isUnit_one, Finset.inf_empty, inf_top_eq]
  | insert j T hj ih =>
    rw [Finset.prod_insert hj, Scheme.basicOpen_mul, Scheme.Hom.preimage_inf, ih, basicOpen_ratioSec,
      Scheme.Hom.preimage_inf, Finset.inf_insert, inf_inf_inf_comm, inf_idem]

theorem rat_eq (φ : Z ⟶ PSpace ℂ d) (a j : Fin (d + 1)) (ha : genericPoint Z ∈ φ ⁻¹ᵁ chart d a) :
    rat φ a j = Z.presheaf.germ (φ ⁻¹ᵁ chart d a) (genericPoint Z) ha (φ.app (chart d a) (ratioSec d a j)) := by
  rw [rat, dite_eq_left ha]

theorem germ_const (p : Z ⟶ Sp ℂ) [inst : Algebra ℂ Z.functionField] (hinst : inst = ffAlg p)
    (φ : Z ⟶ PSpace ℂ d) (hφ : φ ≫ PSpace.str ℂ d = p) (a : Fin (d + 1))
    (ha : genericPoint Z ∈ φ ⁻¹ᵁ chart d a) (c : ℂ) :
    Z.presheaf.germ (φ ⁻¹ᵁ chart d a) (genericPoint Z) ha (φ.app (chart d a) (algebraMap ℂ Γ(PSpace ℂ d, chart d a) c)) =
      algebraMap ℂ Z.functionField c := by
  subst hinst hφ
  rw [GlobalTheory.ProjSpace.algebraMap_sections_eq]
  simp only [Scheme.Hom.appLE, ffAlg, RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp, RingHom.comp_apply,
    Scheme.Hom.comp_appTop]
  generalize (CommRingCat.Hom.hom (Scheme.Hom.app (PSpace.str ℂ d) ⊤))
    ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv) c) = w
  have e := ConcreteCategory.congr_hom (φ.naturality (homOfLE (le_top : chart d a ≤ ⊤)).op) w
  simp only [ConcreteCategory.comp_apply] at e
  erw [e, TopCat.Presheaf.germ_res_apply]
  rfl

theorem germ_mem_adjoin (p : Z ⟶ Sp ℂ) [inst : Algebra ℂ Z.functionField] (hinst : inst = ffAlg p)
    (φ : Z ⟶ PSpace ℂ d) (hφ : φ ≫ PSpace.str ℂ d = p) (a : Fin (d + 1))
    (ha : genericPoint Z ∈ φ ⁻¹ᵁ chart d a) (t : Γ(PSpace ℂ d, chart d a)) :
    Z.presheaf.germ (φ ⁻¹ᵁ chart d a) (genericPoint Z) ha (φ.app (chart d a) t) ∈
      Algebra.adjoin ℂ (Set.range (rat φ a)) := by
  obtain ⟨q, rfl⟩ := GlobalTheory.ProjSpace.aeval_ratio_surjective ℂ d a t
  induction q using MvPolynomial.induction_on with
  | C c => rw [aeval_C, germ_const p hinst φ hφ a ha c]; exact Subalgebra.algebraMap_mem _ c
  | add q r hq hr => rw [map_add (f := _), map_add (f := _), map_add (f := _)]; exact add_mem hq hr
  | mul_X q j hq =>
    rw [map_mul, map_mul, map_mul, aeval_X, ← ratioSec_eq_ratio, ← rat_eq φ a j ha]
    exact mul_mem hq (Algebra.subset_adjoin ⟨j, rfl⟩)

theorem rat_eq_crd [Algebra ℂ Z.functionField] (φ : Z ⟶ PSpace ℂ d) (a j : Fin (d + 1))
    (h0 : genericPoint Z ∈ φ ⁻¹ᵁ chart d 0) (ha : genericPoint Z ∈ φ ⁻¹ᵁ chart d a) :
    rat φ a j = algebraMap (fld φ) Z.functionField (crd φ j / crd φ a) := by
  rw [map_div₀]
  exact (rat_overlap d Z φ 0 a j h0 ha).2

end GlobalTheory.PD.XCover.Integ


open GlobalTheory.PD.XCover.Integ in
theorem GlobalTheory.PD.XCover.germ_mem_rB : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → ∀ (I : Finset (Fin (d + 1))), I.Nonempty → ∀ (h : genericPoint Z ∈ I.inf fun i => φ ⁻¹ᵁ chart d i) (f : Γ(Z, I.inf fun i => φ ⁻¹ᵁ chart d i)), (Z.presheaf.germ _ (genericPoint Z) h).hom f ∈ rB ℂ Z.functionField (crd φ) I := by
  intro d Z _ p _ inst hinst φ _ hφ hgen I hI h f
  obtain ⟨a, ha⟩ := hI
  have hV : IsAffineOpen (chart d a) := GlobalTheory.ProjSpace.isAffineOpen_chart ℂ d a
  have hU : IsAffineOpen (φ ⁻¹ᵁ chart d a) := hV.preimage φ
  have hsub : Algebra.adjoin ℂ (Set.range (rat φ a)) ≤
      (rA ℂ (crd φ) I).map (IsScalarTower.toAlgHom ℂ (fld φ) Z.functionField) := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    exact ⟨crd φ j / crd φ a, Algebra.subset_adjoin ⟨a, ha, j, rfl⟩, (rat_eq_crd φ a j (hgen 0) (hgen a)).symm⟩
  have hint : ∀ y : Γ(Z, φ ⁻¹ᵁ chart d a),
      IsIntegral (rA ℂ (crd φ) I) ((Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom y) := by
    intro y
    obtain ⟨P, hPm, hP⟩ := IsIntegralHom.isIntegral_app φ _ hV y
    set G := (Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom
    have hlift : P.map (G.comp (φ.app (chart d a)).hom) ∈
        Polynomial.lifts (algebraMap (rA ℂ (crd φ) I) Z.functionField) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨x, hx, hxy⟩ := hsub (germ_mem_adjoin p hinst φ hφ a (hgen a) (P.coeff n))
      exact ⟨⟨x, hx⟩, hxy⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hPm.map _)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, Polynomial.eval_map, ← Polynomial.hom_eval₂, hP, map_zero]
  set s := φ.app (chart d a) (∏ i ∈ I, ratioSec d a i) with hs
  have hbo : Z.basicOpen s = I.inf fun i => φ ⁻¹ᵁ chart d i := by
    rw [hs, basicOpen_prod]
    exact inf_eq_right.2 (Finset.inf_le (f := fun i => φ ⁻¹ᵁ chart d i) ha)
  have hgs : (Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom s = ∏ i ∈ I, rat φ a i := by
    rw [hs, map_prod, map_prod]
    exact Finset.prod_congr rfl fun i _ => (rat_eq φ a i (hgen a)).symm
  have hinv : (∏ i ∈ I, rat φ a i)⁻¹ = algebraMap (fld φ) Z.functionField (∏ i ∈ I, crd φ a / crd φ i) := by
    rw [map_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [rat_eq_crd φ a i (hgen 0) (hgen a), ← map_inv₀, inv_div]
  have hne : (∏ i ∈ I, rat φ a i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => (rat_overlap d Z φ a i i (hgen a) (hgen i)).1
  suffices H : ∀ (W : Z.Opens) (hW : W = Z.basicOpen s) (h : genericPoint Z ∈ W) (f : Γ(Z, W)),
      (Z.presheaf.germ _ (genericPoint Z) h).hom f ∈ rB ℂ Z.functionField (crd φ) I from H _ hbo.symm h f
  rintro W rfl h f
  haveI := hU.isLocalization_basicOpen s
  obtain ⟨⟨y, _, n, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers s) f
  dsimp only at e
  have hres : ∀ z : Γ(Z, φ ⁻¹ᵁ chart d a), (Z.presheaf.germ _ (genericPoint Z) h).hom
      (algebraMap Γ(Z, φ ⁻¹ᵁ chart d a) Γ(Z, Z.basicOpen s) z) = (Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom z :=
    fun z => Z.presheaf.germ_res_apply (homOfLE (Z.basicOpen_le s)) _ h z
  have e' := congrArg (Z.presheaf.germ _ (genericPoint Z) h).hom e
  rw [map_mul, hres, hres, map_pow, hgs] at e'
  have hf : (Z.presheaf.germ _ (genericPoint Z) h).hom f =
      (Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom y * ((∏ i ∈ I, rat φ a i)⁻¹) ^ n := by
    rw [inv_pow, ← e', mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hne), mul_one]
  have hr : (∏ i ∈ I, crd φ a / crd φ i) ∈ rA ℂ (crd φ) I :=
    prod_mem fun i hi => Algebra.subset_adjoin ⟨i, hi, a, rfl⟩
  have hA : IsIntegral (rA ℂ (crd φ) I)
      (algebraMap (fld φ) Z.functionField (∏ i ∈ I, crd φ a / crd φ i)) :=
    isIntegral_algebraMap (R := rA ℂ (crd φ) I) (A := Z.functionField) (x := ⟨_, hr⟩)
  rw [hf, hinv]
  exact (Subalgebra.mem_restrictScalars ℂ).2 ((hint y).mul (hA.pow n))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormPullbackDominantStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericGerm_differentialForm_pullback_dominant : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (p : Z ⟶ Sp ℂ) (p' : Z' ⟶ Sp ℂ),
    letI := algΓ p; letI := algΓ p'
    ∀ [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Z'.functionField] (hinst : inst = ffAlg p)
      (hinst' : inst' = ffAlg p') (f : Z' ⟶ Z) (hf : f ≫ p = p') (ψ : Z.functionField →ₐ[ℂ] Z'.functionField)
      (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField), IsDRMap ℂ ψ φ →
      (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Z' ∈ f ⁻¹ᵁ V) (g : Γ(Z, V)),
        ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) =
          (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') hV').hom (f.app V g)) →
      ∀ (j : ℕ) (V : Z.Opens) (V' : Z'.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
        (hη : genericPoint Z ∈ V) (hη' : genericPoint Z' ∈ V') (h : V' ≤ f ⁻¹ᵁ V)
        (y : sectionsOn (Omega p j) V),
        formGermI p' j hV' hη' hinst' (sectionsOn.res ℂ (Omega p' j) h
          (sectionsOn.mapOver (appTop_algebraMap hf) (omegaPull hf j) V y)) =
          φ (formGermI p j hV hη hinst y) := by
  first | (exact @GlobalTheory.HodgeCoh.formGermI_res_mapOver) | (exact GlobalTheory.HodgeCoh.formGermI_res_mapOver) | (intros; apply GlobalTheory.HodgeCoh.formGermI_res_mapOver  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormRestrictAffineOpenStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericGerm_differentialForm_restrict_affineOpen : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ),
    letI := algΓ p
    ∀ [inst : Algebra ℂ Z.functionField] (hinst : inst = ffAlg p) (j : ℕ) (V V' : Z.Opens)
      (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hη : genericPoint Z ∈ V) (hη' : genericPoint Z ∈ V')
      (h : V' ≤ V) (y : sectionsOn (Omega p j) V),
      formGermI p j hV' hη' hinst (sectionsOn.res ℂ (Omega p j) h y) = formGermI p j hV hη hinst y := by
  first | (exact @GlobalTheory.HodgeCoh.formGermI_res) | (exact GlobalTheory.HodgeCoh.formGermI_res) | (intros; apply GlobalTheory.HodgeCoh.formGermI_res  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModuleCubePullHomTermCommCechDifferential
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull

noncomputable section

namespace GlobalTheory.Cube.PullHom

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R S : Type} [Ring R] [Ring S]
  {σ : R →+* S} {τ : κ → ι} {A : Cube.{0} ι R} {B : Cube.{0} κ S} (ψ : Cube.PullHom σ τ A B)


open Classical in
def totalPull (y : ∀ s : Finset ι, A.obj s) (s : Finset κ) : B.obj s :=
  if Set.InjOn τ (s : Set κ) then PD.sortSign τ s • ψ.app s (y (s.image τ)) else 0

theorem term_eq_totalPull {p : ℕ} (x : Cube.Term A p) (s : {s : Finset κ // s.card = p}) :
    ψ.term p x s = totalPull ψ (Cube.extend A p x) s.1 := by
  by_cases h : Set.InjOn τ (s.1 : Set κ)
  · rw [term_apply_of_injOn ψ x s h, totalPull, if_pos h, Cube.extend_apply_of_eq A x (card_image s h)]
  · rw [term_apply_of_not_injOn ψ x s h, totalPull, if_neg h]

theorem totalPull_totalD (y : ∀ s : Finset ι, A.obj s) :
    totalPull ψ (Cube.totalD A y) = Cube.totalD B (totalPull ψ y) := by
  funext t
  rw [Cube.totalD_apply B]
  by_cases h : Set.InjOn τ (t : Set κ)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [totalPull, if_pos h, Cube.totalD_apply A,
      Finset.sum_image (fun x hx y hy hxy => h hx hy hxy), map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : Set.InjOn τ ((t.erase i : Finset κ) : Set κ) :=
        h.mono (Finset.coe_subset.2 (Finset.erase_subset i t))
      rw [totalPull, if_pos hi', map_zsmul, map_zsmul, smul_smul, smul_smul,
        PD.PullMap.sign_inj h hi, ← ψ.app_res]
      congr 2
      exact Cube.res_congr A y (PD.PullMap.image_erase_of_injOn h hi) _ _
  · rw [totalPull, if_neg h]
    obtain ⟨a, ha, b, hb, he, hab⟩ : ∃ a ∈ t, ∃ b ∈ t, τ a = τ b ∧ a ≠ b := by
      by_contra hc
      push_neg at hc
      exact h (fun x hx y hy hxy => hc x hx y hy hxy)
    have zero_of : ∀ s : Finset κ, a ∈ s → b ∈ s → totalPull ψ y s = 0 := fun s has hbs => by
      rw [totalPull, if_neg]
      intro hs
      exact hab (hs has hbs he)
    rw [Finset.sum_eq_add_of_mem a b ha hb hab (fun x _ hne => by
      rw [zero_of _ (Finset.mem_erase.2 ⟨hne.1.symm, ha⟩) (Finset.mem_erase.2 ⟨hne.2.symm, hb⟩),
        map_zero, smul_zero])]
    by_cases hia : Set.InjOn τ ((t.erase a : Finset κ) : Set κ)
    · have hib := PD.PullMap.injOn_erase_swap hb hab he hia
      have key : ∀ c ∈ t, (t.erase c).image τ = t.image τ →
          Cube.res B (Finset.erase_subset c t) (ψ.app (t.erase c) (y ((t.erase c).image τ))) =
            ψ.app t (y (t.image τ)) := by
        intro c _ e
        rw [← ψ.app_res, Cube.res_congr A y e _ (subset_refl _), Cube.res_self]
      rw [totalPull, totalPull, if_pos hia, if_pos hib, map_zsmul, map_zsmul,
        key a ha (PD.PullMap.image_erase_eq hb hab he),
        key b hb (PD.PullMap.image_erase_eq ha hab.symm he.symm), smul_smul, smul_smul, ← add_smul,
        PD.PullMap.sign_pair ha hb hab he hia, neg_add_cancel, zero_smul]
    · have hib : ¬ Set.InjOn τ ((t.erase b : Finset κ) : Set κ) := fun hib =>
        hia (PD.PullMap.injOn_erase_swap ha hab.symm he.symm hib)
      rw [totalPull, totalPull, if_neg hia, if_neg hib, map_zero, map_zero, smul_zero, smul_zero,
        add_zero]

theorem term_d (p : ℕ) (x : Cube.Term A p) :
    ψ.term (p + 1) (Cube.d A p x) = Cube.d B p (ψ.term p x) := by
  funext t
  rw [Cube.d_apply_eq_totalD B (ψ.term p x) (totalPull ψ (Cube.extend A p x))
    (fun s => term_eq_totalPull ψ x s), ← totalPull_totalD]
  by_cases h : Set.InjOn τ (t.1 : Set κ)
  · rw [term_apply_of_injOn ψ _ t h, totalPull, if_pos h, Cube.d_apply_eq_totalD A x (Cube.extend A p x)
      (fun s => (Cube.extend_apply_of_eq A x s.2).symm)]
  · rw [term_apply_of_not_injOn ψ _ t h, totalPull, if_neg h]

end GlobalTheory.Cube.PullHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ProjectiveChartAffineCover
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_chart_affine_cover : ∀ (d : ℕ) (Z : Scheme.{0}) (φ : Z ⟶ PSpace ℂ d) [IsAffineHom φ], (⨆ i, φ ⁻¹ᵁ chart d i) = ⊤ ∧ ∀ I : Finset (Fin (d + 1)), I.Nonempty → IsAffineOpen (I.inf fun i => φ ⁻¹ᵁ chart d i) := by
  first | (exact @GlobalTheory.PD.XCover.preimage_chart_cover) | (exact GlobalTheory.PD.XCover.preimage_chart_cover) | (intros; apply GlobalTheory.PD.XCover.preimage_chart_cover  <;> assumption)
end

