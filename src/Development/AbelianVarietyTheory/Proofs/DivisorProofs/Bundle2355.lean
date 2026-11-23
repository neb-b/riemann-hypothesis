module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteNbhdGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0161
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymLam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2031
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleChartCoveringComplexPoints
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CoverDeg

theorem exists_open_covering_charts : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, genericPoint X ∈ U ∧ ∀ σ : k →+* ℂ, (∀ y ∈ ptsIn p σ U, (PtsOver.map π hπ (spMap σ)  ⁻¹' {y}).encard = (π.residueDegree (genericPoint Y) : ℕ∞)) ∧ (∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) ∧ (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ ptsIn p σ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) := by
  intro k _ X Y _ _ p q D hp hq π hπ hη hδ
  obtain ⟨U₁, hU₁, hx₁, ht⟩ := _root_.GlobalTheory.GenericCoords.exists_affine_etale_coords hp
  obtain ⟨U₂, hU₂, hx₂, hV₂, he₂, hf₂, hr₂⟩ := GlobalTheory.T.exists_affine_etale_finite_nbhd_generic hp hq π hπ hη hδ
  obtain ⟨U, hxU, hG⟩ := GlobalTheory.T.exists_basicOpen_etaleCoordinates_finiteFreeEtaleCover p π D _ _ U₁ U₂ hU₁ hx₁ ht hU₂ hx₂ hV₂ he₂ hf₂ hr₂
  refine ⟨U, hxU, fun σ => ⟨fun y hy => ?_, fun y hy => ?_, fun z hz c hc => ?_⟩⟩
  · rw [_root_.GlobalTheory.encard_fibre_eq_encard_ringHom π hπ U hG.1 hG.2.1 σ y hy]
    exact GlobalTheory.T.encard_complexPoints_finiteEtaleFree_eq_rank (π.app U).hom _ hG.2.2.2.1 hG.2.2.2.2.1 hG.2.2.2.2.2 _
  · obtain ⟨t, ht⟩ := hG.2.2.1
    obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hG.1 t ht hy
    exact ⟨c, hc⟩
  · set y := PtsOver.map π hπ (spMap σ) z with hy
    have hyc : y ∈ ptsIn p σ c.U := c.source_subset hc
    have hpt : ∀ W : X.Opens, y ∈ ptsIn p σ W → π (z.1 (IsLocalRing.closedPoint ℂ)) ∈ W := by
      intro W hW
      have := mem_ptsIn.1 hW
      exact this
    obtain ⟨V, hV, hzV, h, hVe⟩ := _root_.GlobalTheory.CoverDeg.etale_pullback_coords π hπ D _ U hG c.U c.x c.affine c.etale _ (hpt U hz) (hpt c.U hyc)
    obtain ⟨c'', hc'', hU'', hx''⟩ := AlgChart.exists_of_etale (σ := σ) hV _ hVe (mem_ptsIn.2 hzV)
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

end GlobalTheory.CoverDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPicPatch
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PinchLift

theorem exists_pic_patch : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (a : Pic X') (b : Pic Z), GlobalTheory.CechPic.pull i' a = GlobalTheory.CechPic.pull p' b → ∃ e : Pic X, GlobalTheory.CechPic.pull p e = a ∧ GlobalTheory.CechPic.pull i e = b := by
  have hA1 := _root_.GlobalTheory.PinchLift.exists_gen_away_of_closed
  have hA2 := _root_.GlobalTheory.PinchLift.near_matched
  have hB := _root_.GlobalTheory.PinchLift.assemble
  intro X X' Z Z' p i i' p' hsq hp hi hgl a b hab
  obtain ⟨L', hL', rfl⟩ := cls_surj a
  obtain ⟨LZ, hLZ, rfl⟩ := cls_surj b
  rw [← cls_pull hL' i' (pull_isLB hL' i'), ← cls_pull hLZ p' (pull_isLB hLZ p')] at hab
  obtain ⟨w, hw⟩ := (cls_eq_iff _ _).1 hab
  refine hB X X' Z Z' p i i' p' hsq hgl L' LZ hL' hLZ w hw fun x => ?_
  by_cases hx : ∃ z, i z = x
  · obtain ⟨z, rfl⟩ := hx
    exact hA2 X X' Z Z' p i i' p' hsq hp hi hgl L' LZ hL' hLZ w hw z
  · push_neg at hx
    obtain ⟨W, s', hxW, hbot, hs'⟩ := hA1 X X' Z Z' p i i' p' hsq hp hi hgl L' hL' x hx
    have hno : ∀ y : Z, y ∉ i ⁻¹ᵁ W := fun y hy => by rw [hbot] at hy; exact hy
    refine ⟨W, s', fun _ => 1, hxW, hs', fun k l y _ _ hy => (hno y hy).elim,
      fun z j k _ _ hz _ => (hno _ hz).elim⟩

end GlobalTheory.PinchLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointDisjointUnionRepresentingAdditiveFamiStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_disjointUnion_representingAdditiveFamily : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S) (V : κ → X.left.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left], (⨆ i, (j i).left.opensRange = ⊤) → (Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) → ∀ (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X), (∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι) → ∀ (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left), (∀ i, Rep A (b i) (P i)) → Pt.IsLB → (∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) → ∀ (T : Over S) (t : T ⟶ X) (N : LB (A ⊗ T).left), Fam A N → ∃ x : T ⟶ Bt, x ≫ bt = t ∧ LBIso N (ev Pt (fst A T) (snd A T ≫ x)) := by
  first | exact @GlobalTheory.DualCon.ProdGlue.rep_exists | exact GlobalTheory.DualCon.ProdGlue.rep_exists | (intros; apply GlobalTheory.DualCon.ProdGlue.rep_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseGeneratorOfDualNumberLineBundleGeStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pointwiseGenerator_of_dualNumberLineBundleGenerator : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ T, IsEpsGen P v T → ∃ t, IsPtGen P (lift (fst A (epsR R)) (snd A (epsR R) ≫ v)) t := by
  first | exact @GlobalTheory.PtExt.exists_isPtGen_of_isEpsGen | exact GlobalTheory.PtExt.exists_isPtGen_of_isEpsGen | (intros; apply GlobalTheory.PtExt.exists_isPtGen_of_isEpsGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedSpecializationField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem lamPts_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B']
    {φ : B'.left ⟶ B.left} (hB : IsGrpPullback B' B f φ) {T' : Over S'} {T : Over S} (h : Over.mk (T'.hom ≫ f) ⟶ T)
    (x' y' : T' ⟶ B') (x y : T ⟶ B) (hx : x'.left ≫ φ = h.left ≫ x.left) (hy : y'.left ≫ φ = h.left ≫ y.left)
    (k : Fin 4) : lamPts x' y' k ≫ φ = h.left ≫ lamPts x y k := by
  fin_cases k
  · have e := hB.2 T' x' y' (h ≫ x) (h ≫ y) (by rw [Over.comp_left, hx]) (by rw [Over.comp_left, hy])
    show (x' * y').left ≫ φ = h.left ≫ (x * y).left
    rw [← e, ← MonObj.comp_mul, Over.comp_left]
  · exact hx
  · exact hy
  · show (1 : T' ⟶ B').left ≫ φ = h.left ≫ (1 : T ⟶ B).left
    have e := hB.2 T' 1 1 (pushPt hB.1.w 1) (pushPt hB.1.w 1) rfl rfl
    rw [_root_.mul_one] at e
    have e1 : pushPt hB.1.w (1 : T' ⟶ B') = 1 := by
      have : pushPt hB.1.w (1 : T' ⟶ B') * pushPt hB.1.w 1 = pushPt hB.1.w 1 := Over.OverMorphism.ext e
      exact mul_eq_left.1 this
    have e2 : (pushPt hB.1.w (1 : T' ⟶ B')).left = (1 : T' ⟶ B').left ≫ φ := rfl
    rw [← e2, e1, ← Over.comp_left, MonObj.comp_one]

theorem fibre_exists : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (gQ : ℕ) (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]
  (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (K : Type) [Field K] (ev : V₁ →+* K),
  ∃ (P' : PolAV (Sp K)) (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ P'.A.left) (B : Over (Sp K)) (_ : GrpObj B)
    (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
    P'.g = 8 * gQ ∧ IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) P'.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (P'.L.pull ψ) ∧
    E8Fibration.IsPPFib B gQ M ∧ E8Fibration.IsProd pr ∧ E8Fibration.IsE8WeightedBundle W pr P'.L M.L ∧
    ∀ (n : ℕ) (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ n = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ y' : Out.baseOver (Sp K) ⟶ P'.A, y'.left = q ≫ ψ ∧ y' ^ n = 1 := by
  intro W gQ V V₁ _ _ _ _ Q hQ ρ hρ D e hS K _ ev
  have hS' := hS
  obtain ⟨pr₀, w, hmon, huniv, hw, -, -⟩ := hS'
  obtain ⟨P', φ, hφ, hg, hm, t, ht⟩ := GlobalTheory.polBaseChange_holds _ _ (spMap ev) D.P
  have hgp : IsGrpPullback P'.A D.P.A (spMap ev) φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ.w y), ← hm]
    rfl⟩
  obtain ⟨i, hi, hiφ⟩ := grpPullback_iso (isGrpPullback_pullback D.P.A (spMap ev)) hgp
  haveI := hi
  have hinv : i.inv.left ≫ pullback.fst D.P.A.hom (spMap ev) = φ := by
    rw [← hiφ, ← Category.assoc, ← Over.comp_left, i.inv_hom_id, Over.id_left, Category.id_comp]

  have hQP : IsPPFib Q.B Q.g Q.M := ⟨Q.isAb, Q.smoothDim, ⟨Q.cub⟩, Q.ample, Q.ktriv⟩
  obtain ⟨M₁, hM₁, hP₁⟩ := _root_.GlobalTheory.Poinc.Sep.E8Fibration.isPPFib_baseChange (spMap ρ) Q.B Q.g Q.M hQP
  obtain ⟨M, hM, hP⟩ := _root_.GlobalTheory.Poinc.Sep.E8Fibration.isPPFib_baseChange (spMap ev) _ Q.g M₁ hP₁
  let B₁ := (Over.pullback (spMap ρ)).obj Q.B
  let pr : Fin 8 → (P'.A ⟶ (Over.pullback (spMap ev)).obj B₁) :=
    fun a => i.inv ≫ (Over.pullback (spMap ev)).map (pr₀ a)
  have hpr : IsProd pr := _root_.GlobalTheory.Poinc.Sep.E8Fibration.isProd_pullback_iso (spMap ev) pr₀ ⟨hmon, huniv⟩ P'.A i hi
  refine ⟨P', i.hom.left, (Over.pullback (spMap ev)).obj B₁, inferInstance, M, pr, ?_, isGrpPullback_of_iso i, ?_,
    hQ ▸ hP, hpr, ?_, ?_⟩
  · rw [hg, _root_.GlobalTheory.Poinc.Sep.sharpRef_relDim W V V₁ Q ρ D e hS, hQ]
  · have ht' : LBIso (D.P.L.pull φ) P'.L := ⟨t, ht⟩
    exact LBIso.trans (LB.isLB_pull D.P.isLB _) (LB.isLB_pull (LB.isLB_pull D.P.isLB _) _) (LB.isLB_pull P'.isLB _)
      (GlobalTheory.GenSpread.lbIso_pull_pull D.P.isLB i.hom.left hiφ.symm) (GlobalTheory.GenSpread.lbIso_pullback ht' i.hom.left)
  · have ht' : LBIso (D.P.L.pull φ) P'.L := ⟨t, ht⟩
    have H : LBIso M.L (Q.M.L.pull (pullback.fst B₁.hom (spMap ev) ≫ pullback.fst Q.B.hom (spMap ρ))) := by
      rw [hM, hM₁]
      exact LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull Q.M.isLB _ rfl)
    have hx : ∀ a, (pr a).left ≫ pullback.fst B₁.hom (spMap ev) = φ ≫ (pr₀ a).left := fun a => by
      show (i.inv ≫ (Over.pullback (spMap ev)).map (pr₀ a)).left ≫ _ = _
      rw [Over.comp_left, Category.assoc]
      have hp : ((Over.pullback (spMap ev)).map (pr₀ a)).left ≫ pullback.fst B₁.hom (spMap ev) =
          pullback.fst D.P.A.hom (spMap ev) ≫ (pr₀ a).left := pullback.lift_fst _ _ _
      rw [hp, ← Category.assoc, hinv]
    have ha := GlobalTheory.ShapePull.iso_linComb_pull H (fun k : (Fin 8 × Fin 8) × Fin 4 => lamPts (pr k.1.1) (pr k.1.2) k.2)
      (fun k => lamPts (pr₀ k.1.1) (pr₀ k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)) φ
      (fun k => by
        rw [← Category.assoc, lamPts_pull (isGrpPullback_pullback B₁ (spMap ev)) (Over.homMk φ hφ.w) (pr k.1.1) (pr k.1.2)
          (pr₀ k.1.1) (pr₀ k.1.2) (hx _) (hx _) k.2, Category.assoc]
        rfl)
    have hb := GlobalTheory.GenSpread.lbIso_pullback (⟨w, hw⟩ : LBIso D.P.L _) φ
    exact LBIso.trans P'.isLB (LB.isLB_pull D.P.isLB _) (LB.isLB_linComb M.isLB _ _) (LBIso.symm ht')
      (LBIso.trans (LB.isLB_pull D.P.isLB _) (LB.isLB_pull (LB.isLB_linComb Q.M.isLB _ _) _) (LB.isLB_linComb M.isLB _ _)
        hb (LBIso.symm ha))
  · intro n y hy q hq1 hq2
    have hw' : (q ≫ i.hom.left) ≫ P'.A.hom = (baseOver (Sp K)).hom := by
      rw [Category.assoc, Over.w i.hom]
      exact hq2
    refine ⟨Over.homMk (q ≫ i.hom.left) hw', rfl, ?_⟩
    rw [← GlobalTheory.Raynaud.pow_eq_one_iff_of_isGrpPullback hgp]
    let c : Over.mk (spMap ev) ⟶ Over.mk ((baseOver (Sp K)).hom ≫ spMap ev) := Over.homMk (𝟙 _) (by simp)
    let c' : Over.mk ((baseOver (Sp K)).hom ≫ spMap ev) ⟶ Over.mk (spMap ev) := Over.homMk (𝟙 _) (by simp)
    have hcc : c' ≫ c = 𝟙 _ := by ext; simp [c, c']
    have hy' : c ≫ pushPt hgp.1.w (Over.homMk (q ≫ i.hom.left) hw' : baseOver (Sp K) ⟶ P'.A) = y := by
      ext
      show 𝟙 _ ≫ (q ≫ i.hom.left) ≫ φ = y.left
      rw [Category.id_comp, Category.assoc, hiφ, hq1]
    have h1 : c ≫ pushPt hgp.1.w (Over.homMk (q ≫ i.hom.left) hw' : baseOver (Sp K) ⟶ P'.A) ^ n = 1 := by
      rw [MonObj.comp_pow, hy', hy]
    have h2 := congrArg (c' ≫ ·) h1
    simp only [← Category.assoc, hcc, Category.id_comp, MonObj.comp_one] at h2
    exact h2

end GlobalTheory.Poinc.Sep.E8Fibration
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveRiemannFormOfRelAmpleExponential
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory

theorem im_dot_mulVec_star_zsmul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℤ) (v w : Fin g → ℂ) :
    ((c • v) ⬝ᵥ Hm *ᵥ star w).im = c * (v ⬝ᵥ Hm *ᵥ star w).im := by
  rw [smul_dotProduct, zsmul_eq_mul, Complex.mul_im]
  simp

theorem im_dot_mulVec_star_zsmul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℤ) (v w : Fin g → ℂ) :
    (v ⬝ᵥ Hm *ᵥ star (c • w)).im = c * (v ⬝ᵥ Hm *ᵥ star w).im := by
  rw [star_zsmul, Matrix.mulVec_smul, dotProduct_smul, zsmul_eq_mul, Complex.mul_im]
  simp

theorem exists_riemannForm_of_relAmple : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (L : LB G.left), L.IsLB → Out.RelAmple G L → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (La : Type) [AddCommGroup La] (P : La →+ (Fin g → ℂ)), IsExp y e → Function.Injective P → (∀ z, e z = 1 ↔ z ∈ P.range) → ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La), Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ (∀ x x', (hermForm Hm (P x) (P x')).im = EF x x') ∧ (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs G L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) := by
  intro X G _ _ g hG hsm L hL hamp y e La _ P he hP hker
  obtain ⟨Λ, hd, hfull, hΛ⟩ := _root_.GlobalTheory.ExpKernel.kernel_isFullLattice X G g hG hsm y e he
  obtain ⟨hadd, honto, hhol, -, -⟩ := he
  letI : GrpObj ((Over.pullback y).obj G) := Functor.grpObjObj
  haveI : IsCommMonObj ((Over.pullback y).obj G) := Functor.isCommMonObj_obj
  have hp : IsGrpPullback ((Over.pullback y).obj G) G y (pullback.fst G.hom y) := isGrpPullback_pullback G y
  have hLA : (L.pull (pullback.fst G.hom y)).IsLB := LB.isLB_pull hL _
  obtain ⟨hA, hampA, -⟩ := GlobalTheory.pol_pull X (Sp ℂ) G ((Over.pullback y).obj G) y (pullback.fst G.hom y) L
    (L.pull (pullback.fst G.hom y)) hL hLA hG hp (GlobalTheory.PolBaseChange.lbIso_refl hLA)
  let L₀ : LB G.left := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
  let u₀ : HolUnif ((Over.pullback y).obj G) (L₀.pull (pullback.fst G.hom y)) g :=
    GlobalTheory.OrthoMetric.fibreUnif hp (L := L₀) e Λ.toAddSubgroup (fun _ _ => 1) hadd honto hΛ hd hfull hhol
      (fun _ => differentiableOn_const _) (fun _ _ _ => one_ne_zero)
      (fun j j' z hz => by
        show (1 : ℂ) = valAt' (e z).left (⊤ ⊓ ⊤) (1 : Γ(G.left, ⊤ ⊓ ⊤)ˣ).val * 1
        rw [_root_.mul_one]
        exact (valAt'_one _ hz).symm)
  obtain ⟨u, Hm, χ, hex, hF⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif _ hA _ g u₀ _ hLA
  have hpos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple _ hA _ hLA (hampA hamp) g u Hm χ hF.1 hF.2.1 hF.2.2
  have hAH : u.IsAH Hm χ := GlobalTheory.TorusRM.isAH_of_isFactorAH hF hpos
  have huΛ : ∀ z, z ∈ u.Λ ↔ z ∈ P.range := fun z => by
    rw [← u.ker, hex]
    exact (u₀.ker z).trans ((hΛ z).symm.trans (hker z))
  have hmem : ∀ a, P a ∈ u.Λ := fun a => (huΛ _).2 ⟨a, rfl⟩
  choose N hN using fun a b => GlobalTheory.TorusRM.ahFactor_im_int g _ _ u Hm χ hLA hF (P a) (hmem a) (P b) (hmem b)
  let EF : LinearMap.BilinForm ℤ La := LinearMap.mk₂ ℤ N
    (fun a a' b => Int.cast_injective (α := ℝ) (by
      push_cast; rw [← hN, ← hN, ← hN, map_add (f := _), add_dotProduct, Complex.add_im]))
    (fun c a b => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, ← hN, ← hN, map_zsmul]
      exact im_dot_mulVec_star_zsmul_left Hm c _ _))
    (fun a b b' => Int.cast_injective (α := ℝ) (by
      push_cast; rw [← hN, ← hN, ← hN, map_add (f := _), star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im]))
    (fun c a b => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, ← hN, ← hN, map_zsmul]
      exact im_dot_mulVec_star_zsmul_right Hm c _ _))
  have hEF : ∀ a b, EF a b = N a b := fun _ _ => rfl
  have tr : ∀ (t : Sp ℂ ⟶ X), (𝟙_ (Over (Sp ℂ))).hom ≫ y = t → ∀ (k : ℤ)
      (x x' : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback y).obj G) (x₀ x₀' : Over.mk t ⟶ G) (c : Γ(Sp ℂ, ⊤)ˣ),
      x₀.left = x.left ≫ pullback.fst G.hom y → x₀'.left = x'.left ≫ pullback.fst G.hom y →
      Out.WeilIs _ (L.pull (pullback.fst G.hom y)) k x x' c → Out.WeilIs G L k x₀ x₀' c := by
    intro t ht
    subst ht
    intro k x x' x₀ x₀' c h1 h2 hw
    exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm X (Sp ℂ) G _ y _ L _ hL hLA hp
      (GlobalTheory.PolBaseChange.lbIso_refl hLA) (𝟙_ _) k x x' x₀ x₀' c h1 h2).1 hw
  have hexl : ∀ z, (e z).left = (u.ex z).left ≫ pullback.fst G.hom y := fun z => by
    rw [hex]
    exact (GlobalTheory.OrthoMetric.liftPt_comp hp (e z)).symm
  refine ⟨Hm, EF, hF.1, fun z hz => hpos z hz, fun x x' => (hN x x').trans (by rw [hEF]), ?_⟩
  intro k a b c hk hc
  have hw := GlobalTheory.AHWeilAny.weilIs_exp_riemannForm _ hA _ hLA g u Hm χ hAH k (P a) (P b) c hk (hmem a) (hmem b)
    (by rw [hc, hN a b, hEF, Complex.ofReal_intCast])
  exact tr y (Category.id_comp y) k _ _ _ _ _ (hexl _) (hexl _) hw

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipal
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PrincipalOfPairing

open GlobalTheory.CechPic

theorem lbIso_sq_diag {k : Type} [Field k] [IsAlgClosed k] {B : Over (Sp k)} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {L : LB B.left} (hL : L.IsLB) (hs : Out.Sym B L) {P : LB (G2 B).left} (hP : P.IsLB)
    (hiso : LBIso (abelian₂ B L) P) : LBIso (lbPow L 2) (P.pull (lift (𝟙 B) (𝟙 B) : B ⟶ G2 B).left) := by
  have hlam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hPow : (lbPow L 2).IsLB := LB.isLB_linComb hL _ _
  have hΘ := exists_gen_theta_of_isAbelianScheme k B hB L hL
  have h₀ : pull (1 : B ⟶ B).left (cls L hL) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    obtain ⟨N, hN, e⟩ := cls_surj (pull (η[B]).left (cls L hL))
    have z : cls N hN = 0 := (cls_eq_zero_iff hN).2 (DVR.exists_gen_of_isLB_local (V := k) N hN)
    rw [← e, z, map_zero]
  have h₁ : cls _ hlam = lam (cls L hL) (fst B B) (snd B B) := cls_cube_two hL _ _ hlam
  have h₂ := lam_mul_left hL hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)
  rw [mul_inv_cancel, lam_one_left, lam.eq_1 _ (𝟙 B)⁻¹, inv_mul_cancel, h₀] at h₂
  have h₃ := exists_gen_neg_of_sym GlobalTheory.lawsAndExpansions.1.1.globalFns hB hL hs
  rw [← cls_eq_zero_iff (LB.isLB_linComb hL _ _), cls_linComb hL] at h₃
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id] at h₃
  have einv : GrpObj.inv (X := B) = (𝟙 B)⁻¹ := by simp [Hom.inv_def]
  rw [einv, add_neg_eq_zero] at h₃
  rw [h₃, Over.id_left, pull_id] at h₂
  refine (cls_eq_iff hPow (pull_isLB hP _)).1 ?_
  rw [cls_lbPow hL 2 hPow, cls_pull hP, ← (cls_eq_iff hlam hP).2 hiso, h₁, pull_lam, lift_fst, lift_snd,
    eq_neg_of_add_eq_zero_left h₂.symm, two_smul]
  abel

theorem exists_principal : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → Out.RelAmple A (PP.pull (lift (𝟙 A) (𝟙 A) : A ⟶ G2 A).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : LB.Gen (PP.pull (lift (snd A T ≫ x) (fst A T) : A ⊗ T ⟶ G2 A).left), t.IsGen) → x = toUnit T ≫ η[A]) → ∃ L : LB A.left, L.IsLB ∧ Out.Sym A L ∧ LBIso (abelian₂ A L) PP ∧ Out.RelAmple A L ∧ Out.KTriv A L := by
  intro K _ _ _ A _ _ hA P hP hs hb ha hk
  obtain ⟨L, hL, sL, iL⟩ := GlobalTheory.SymBiextHalf.exists_sym_lam K A hA P hP hs hb
  refine ⟨L, hL, sL, iL, ?_, GlobalTheory.KTrivOfLam.kTriv_of_lam_iso _ A hA P hP hk L hL iL⟩
  have := hA.proper
  have hMa := isAmpleLB_of_relAmple_of_isAffine A (pull_isLB hP _) ha
  have h2 : IsAmpleLB (lbPow L 2) := hMa.of_lbIso (isLB_lbPow hL 2) (lbIso_sq_diag hA hL sL hP iL)
  have hLa : IsAmpleLB L := (isAmpleLB_pow_iff hL (by norm_num)).1 h2
  refine relAmple_of_isAmpleLB A hL fun U hU => ?_
  have : CompactSpace (A.hom ⁻¹ᵁ U) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := A.hom) _ U.isOpen hU.isCompact)
  exact hLa.pull_of_isOpenImmersion _

end GlobalTheory.PrincipalOfPairing

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiGeneratorsDegenerationLawsSymmetricBalaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_psi_generators_degenerationLaws_symmetricBalanced : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D₀.X] (onB : D₀.P.OAct O), (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) →
    ∀ w0 : O, w0 + star w0 = 1 → ∀ uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ (onB.act w0)) GlobalTheory.UTau0.w0ε), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ τ' : ∀ y z : D₀.X, LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.PolDeg.lamPts (D₀.c y) (D₀.c z)) GlobalTheory.PolDeg.negε),
    GlobalTheory.UTau0.BalTau ⟨D₀.P.L, D₀.rig, D₀.P.isLB, D₀.rig_gen⟩ D₀.cub onB.toRingAct D₀.c τ' →
    (∀ y z p J, Good D₀.P.L p J → val (τ' y z) (𝟙 _) p J = val (τ' z y) (𝟙 _) p J) →
    ∃ ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1)),
      GlobalTheory.UTau0.RLaws D₀ onB w0 uw ψ := by
  first | exact @GlobalTheory.UTau0.exists_psi_rLaws | exact GlobalTheory.UTau0.exists_psi_rLaws | (intros; apply GlobalTheory.UTau0.exists_psi_rLaws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLiftHomAffinePair
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem exists_lift_pair_hom (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X)
    (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀)
    (hi : φ₀ ≫ D.i = D'.i ≫ φ) (p : Pair φ) :
    ∃ θ : Λ.L.obj (Opposite.op p.1.2) ⟶ m.obj (Λ'.L.obj (Opposite.op p.1.1)),
      ∀ a, θ.φ (Λ.e (Opposite.op p.1.2) a) = Λ'.e (Opposite.op p.1.1) (CechDR.secPull D.s D'.s p a) := by
  let T' := Λ'.L.obj (Opposite.op p.1.1)
  let e' : Sec D'.s p.1.1.1 →+* T'.B := Λ'.e (Opposite.op p.1.1)
  let y₀ : Sec D.s p.1.2.1 →+* (m.obj T').B := e'.comp (CechDR.secPull D.s D'.s p)
  have hy : ∀ r : D.R, y₀ (algebraMap D.R _ r) = algebraMap D.R (m.obj T').B r := by
    intro r
    have h1 := semiHom_secPull hφ p r 1
    rw [map_one, ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at h1
    change e' (CechDR.secPull D.s D'.s p (algebraMap D.R _ r)) = algebraMap D'.R T'.B (σ r)
    rw [h1]
    exact (Λ'.e (Opposite.op p.1.1)).commutes _
  let y : Sec D.s p.1.2.1 →ₐ[D.R] (m.obj T').B := { y₀ with commutes' := hy }
  refine ((_root_.GlobalTheory.PDForm.Lift.hom_spec D Λ).1 (Opposite.op p.1.2) (m.obj T') y).1 ?_
  change spMap ((T'.π.comp e').comp (CechDR.secPull D.s D'.s p)) ≫ affPt D.s p.1.2 = (T'.x ≫ φ₀) ≫ D.i
  rw [Cris.spMap_comp, Category.assoc, secPull_affPt, ← Category.assoc, Category.assoc T'.x, hi, ← Category.assoc]
  exact congrArg (· ≫ φ) (Λ'.pt (Opposite.op p.1.1))

end GlobalTheory.PDForm
end

