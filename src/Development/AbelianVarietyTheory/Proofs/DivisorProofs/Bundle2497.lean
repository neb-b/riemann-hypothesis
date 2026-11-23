module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1385
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2298
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
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
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2428
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnLogNorm
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchIntAlter

open Set

variable {k : Type} [CommRing k] {Y Y' : Scheme.{0}} [IsIntegral Y] [IsIntegral Y'] {q : Y ⟶ Sp k}
  {σ : k →+* ℂ}

theorem continuousOn_logNorm {L : LB Y} (φ : Weight q σ L) {r : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) (hφ : φ.IsCInf) :
    ContinuousOn (logNorm φ r) (offSupp q σ (divOfRatSec φ.isLB hr)) := by
  intro y hy
  have ho := isOpen_offSupp (q := q) (σ := σ) (divOfRatSec φ.isLB hr)
  have hi : y ∈ ptsIn q σ (L.U (pick φ.isLB y)) := mem_pick _ y
  have hu := hr.unitAt φ.isLB hy hi
  have hn : ptsIn q σ (L.U (pick φ.isLB y)) ∩ offSupp q σ (divOfRatSec φ.isLB hr) ∈ 𝓝 y :=
    inter_mem ((isOpen_ptsIn _).mem_nhds hi) (ho.mem_nhds hy)
  refine ContinuousAt.continuousWithinAt ?_
  have hc : ContinuousAt (fun z => Real.log ‖ratVal (r (pick φ.isLB y) : Y.functionField) z‖ -
      φ.φ (pick φ.isLB y) z / 2) y :=
    ((LogNormInt.continuousAt_ratVal hu.regAt).norm.log (norm_ne_zero_iff.2 (ratVal_ne_zero hu))).sub
      ((hφ _ y hi).continuousAt.div_const 2)
  refine hc.congr ?_
  filter_upwards [hn] with z hz
  exact (logNorm_eq φ hr hz.2 hz.1).symm

variable (M : HermLB q) (ρ : Y' ⟶ Y) (hη : ρ (genericPoint Y') ⤳ genericPoint Y)
  {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)

theorem mem_offSupp_pull {y : CxPts (ρ ≫ q) σ}
    (hy : y ∈ ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) :
    y ∈ offSupp (ρ ≫ q) σ ((M.restr ρ).div (MultPull.isRatSec_pull_map ρ hη hr)) := by
  have hx : PtsOver.map ρ rfl _ y ∈ offSupp q σ (M.div hr) := mem_ptsIn.2 (mem_ptsIn.1 hy)
  obtain ⟨c, hc⟩ := exists_chart (M.restr ρ).isLB (under y)
  have hc' : PtsOver.map ρ rfl _ y ∈ ptsIn q σ (M.B.U (c PUnit.unit)) :=
    mem_ptsIn.2 (Set.mem_iInter.1 hc PUnit.unit)
  have hu := hr.unitAt M.isLB hx hc'
  have hu' := FrameGlue.Pull.unitAt_fnMap ρ hη hu
  exact mem_offSupp.2 fun h => ((presents_divOfRatSec (M.restr ρ).isLB
    (MultPull.isRatSec_pull_map ρ hη hr)).isEqn c _ hc).mem_supp_iff.1 h hu'

theorem logNorm_pull {y : CxPts (ρ ≫ q) σ}
    (hy : y ∈ ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) :
    logNorm ((M.restr ρ).φ σ) (fun c => Units.map (TrueGeo.SmallSec.fnMap ρ hη).toMonoidHom
      (r (c PUnit.unit))) y = logNorm (M.φ σ) r (PtsOver.map ρ rfl _ y) := by
  have hx : PtsOver.map ρ rfl _ y ∈ offSupp q σ (M.div hr) := mem_ptsIn.2 (mem_ptsIn.1 hy)
  have hj : y ∈ ptsIn _ σ ((M.restr ρ).B.U (pick ((M.restr ρ).φ σ).isLB y)) := mem_pick _ y
  have hj' : PtsOver.map ρ rfl _ y ∈
      ptsIn q σ (M.B.U (pick ((M.restr ρ).φ σ).isLB y PUnit.unit)) :=
    mem_ptsIn.2 (Set.mem_iInter.1 (mem_ptsIn.1 hj) PUnit.unit)
  have hu := hr.unitAt M.isLB hx hj'
  have hu' := FrameGlue.Pull.unitAt_fnMap ρ hη hu
  have e₁ : ((M.restr ρ).φ σ).φ (pick ((M.restr ρ).φ σ).isLB y) y =
      (M.φ σ).φ (pick ((M.restr ρ).φ σ).isLB y PUnit.unit) (PtsOver.map ρ rfl _ y) :=
    (M.φ σ).pull_φ ρ rfl _ y
  have e₂ : ratVal ((Units.map (TrueGeo.SmallSec.fnMap ρ hη).toMonoidHom
      (r (pick ((M.restr ρ).φ σ).isLB y PUnit.unit)) : Y'.functionFieldˣ) : Y'.functionField) y =
      ratVal (r (pick ((M.restr ρ).φ σ).isLB y PUnit.unit) : Y.functionField)
      (PtsOver.map ρ rfl _ y) := by
    show ratVal (TrueGeo.SmallSec.fnMap ρ hη (r (pick ((M.restr ρ).φ σ).isLB y PUnit.unit) :
      Y.functionField)) y = _
    rw [TrueGeo.SmallSec.ratVal_eq_valAt y hu'.regAt, TrueGeo.SmallSec.valAt_fnMap ρ hη _ hu.regAt,
      TrueGeo.SmallSec.ratVal_eq_valAt _ hu.regAt]
    rfl
  rw [logNorm_eq (M.φ σ) hr hx hj', logNorm, e₁, e₂]

end GlobalTheory.ArchIntAlter

namespace GlobalTheory.ArchIntAlter

open Set

end GlobalTheory.ArchIntAlter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnMixedChernFormDensityInChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace GlobalTheory.Mix

theorem continuousOn_dens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (D : ℕ) (L : Fin D → MLine p σ) (c : AlgChart p σ D), ContinuousOn (dens L c) c.e.source := by
  intro k _ X p σ D L c y₀ hy₀
  let i : ∀ a, (L a).B.ι := fun a => pick (L a).φ.isLB y₀
  let S : Set (CxPts p σ) := c.e.source ∩ ⋂ a, ptsIn p σ ((L a).B.U (i a))
  have hSo : IsOpen S := c.e.open_source.inter (isOpen_iInter_of_finite fun a => isOpen_ptsIn _)
  have hy₀S : y₀ ∈ S := ⟨hy₀, mem_iInter.2 fun a => mem_pick _ y₀⟩
  have hH : ∀ (a : Fin D) (j l : Fin D),
      ContinuousOn (fun y => c.hess (L a).φ (i a) y j l) S := by
    intro a j l
    have hO : IsOpen (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ ((L a).B.U (i a))) :=
      isOpen_over c.e (isOpen_ptsIn _)
    have hg : ContDiffOn ℝ ∞ (fun v => ((L a).φ.φ (i a) (c.e.symm v) : ℂ))
        (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ ((L a).B.U (i a))) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_chart ((L a).cInf (i a)) c)
    have hw := ReciprocityTheory.L2DbarEstimates.Y.continuousOn_wd_wdb hO hg j l
    exact hw.comp (c.e.continuousOn.mono inter_subset_left) fun y hy =>
      ⟨c.e.map_source hy.1, by
        simpa only [mem_preimage, c.e.left_inv hy.1] using mem_iInter.1 hy.2 a⟩
  let F : CxPts p σ → ℝ := fun y => (Real.pi ^ D)⁻¹ * (∑ τ : Equiv.Perm (Fin D),
    (Matrix.of fun j l => c.hess (L (τ l)).φ (i (τ l)) y j l).det).re
  have hF : ContinuousOn F S := by
    refine continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      (continuousOn_finsetSum _ fun τ _ => ?_))
    refine (continuous_id.matrix_det).comp_continuousOn ?_
    exact continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hH (τ l) j l
  have he : ∀ y ∈ S, dens L c y = F y := by
    intro y hy
    have hm : ∀ τ : Equiv.Perm (Fin D),
        (Matrix.of fun j l => c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB y) y j l) =
          Matrix.of fun j l => c.hess (L (τ l)).φ (i (τ l)) y j l := fun τ => by
      ext j l
      simp only [Matrix.of_apply]
      rw [c.hess_eq (L (τ l)).cInf hy.1 (mem_iInter.1 hy.2 (τ l)) (mem_pick _ y)]
    simp only [dens, F, hm]
  refine ContinuousAt.continuousWithinAt ?_
  refine (hF.continuousAt (hSo.mem_nhds hy₀S)).congr ?_
  filter_upwards [hSo.mem_nhds hy₀S] with y hy
  exact (he y hy).symm

end GlobalTheory.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMapOfTorMatch
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.TorCoord

theorem coordMap_of_torMatch : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), Function.Injective g → IsGrpPullback G' G (spMap g) β → LBIso U'.LG.L (U.LG.L.pull β) → ∀ ρ, TorMatch U U' g β ρ → CoordMap D.toPre D'.toPre g ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hVb hV G' _ _ hG' D' A' U' g β hg hβ hL ρ hT
  haveI := hV
  let gK : FractionRing R →+* FractionRing V := IsFractionRing.lift (A := R) (K := FractionRing R)
    (g := (algebraMap V (FractionRing V)).comp g) ((IsFractionRing.injective V (FractionRing V)).comp hg)
  have hgK : ∀ r, gK (algebraMap R _ r) = algebraMap V _ (g r) := IsFractionRing.lift_algebraMap _
  refine GlobalTheory.PsiFromTauEven.main R V hV g gK hgK D.toPre D'.toPre D.tau_bimult D.psi_even D'.tau_bimult D'.psi_even ρ ?_
  intro a b x x' hx hx'
  obtain ⟨⟨-, -, -, hVc⟩, hV0⟩ := id hVb
  haveI := hVc
  haveI := hV0
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ IsUnit (l : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by simpa using h⟩
    · exact ⟨2, le_rfl, by simpa using h.neg⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let F := AlgebraicClosure (FractionRing V)
  letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing V) F).comp gK).toAlgebra
  have hF : ∀ y, algebraMap (FractionRing R) F y = algebraMap (FractionRing V) F (gK y) := fun _ => rfl
  have hFr : ∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r)) :=
    fun r => (hF _).trans (congrArg _ (hgK r))
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.exists_genericPoints_uniformisations_weilPairing_galois R hR G hG D A U V hVb hV g hg G' β hβ hG' D' A' U' hL F hFr
  have hm : ∀ (k : ℕ), IsUnit (k : R) → ∀ (τ : Multiplicative D.toPre.X →* Fˣ) (τ' : Multiplicative D'.toPre.X →* Fˣ)
      (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := V) F ⟶ A'.A),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g →
      q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g → QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' → a = e a' := by
    intro k hk τ τ' q q' a a' h1 h2 h3 h4 h5 h6 h7 h8
    have h := (hT F hFr k hk τ τ' q q' a a' h1 h2 h3 h4 h5 h6 h7 h8).trans (he3 a').symm
    simp only [genMap] at h
    have hs : ∀ z : TFK (R := R) F ⟶ A.A, z.left ≫ U.gen.inv.left ≫ pullback.snd G.hom (jK R) = (TFK (R := R) F).hom := by
      intro z
      have := Over.w U.gen.inv
      rw [← Over.w z, ← this]
      rfl
    have h' : a.left ≫ U.gen.inv.left = (e a').left ≫ U.gen.inv.left :=
      pullback.hom_ext (by simpa only [Category.assoc] using h) (by simpa only [Category.assoc] using (hs a).trans (hs (e a')).symm)
    ext1
    have hi : Mono U.gen.inv.left := inferInstance
    exact (cancel_mono _).1 h'
  have key : ∀ k : ℕ, IsUnit (k : R) →
      (k : ℤ) ∣ (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun (Units.map gK.toMonoidHom x) - (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun x' :=
    fun k hk => by
      obtain ⟨O, φ, σ, π, h₁, h₂, h₃, h₄, h₅⟩ := _root_.GlobalTheory.InertiaTameRoot.exists_inertia_moves_root V F ϖ hϖ k (by simpa using hk.map g)
      exact GlobalTheory.TauFormGen.dvd_ord_sub R hR G hG D A U V hVb G' hG' D' A' U' g gK hgK F hF k hk ϖ hϖ O φ σ π h₁ h₂ h₃ h₄ h₅ ρ e
        (he1 k) (he2 σ) (hm k hk) a b x x' hx hx'
  obtain ⟨u, hu⟩ := GlobalTheory.TauForm.exists_unit_of_ord_eq (W := V) (x := Units.map gK.toMonoidHom x) (y := x') (by
    rw [← sub_eq_zero]
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (key (l ^ Int.natAbs
      ((GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun (Units.map gK.toMonoidHom x) - (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun x'))
      (by simpa using hl.pow _)) ?_
    rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self (by omega))
  exact ⟨u, hu⟩

end GlobalTheory.Poinc.TorCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateMapEtaleNearProperFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibEt

@[reassoc]
theorem map_fst' {X Y Z X' Y' Z' : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z') (i₁ : X ⟶ X')
    (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z') (h1 : f ≫ i₃ = i₁ ≫ f') (h2 : g ≫ i₃ = i₂ ≫ g') :
    pullback.map f g f' g' i₁ i₂ i₃ h1 h2 ≫ pullback.fst f' g' = pullback.fst f g ≫ i₁ :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem map_snd' {X Y Z X' Y' Z' : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z') (i₁ : X ⟶ X')
    (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z') (h1 : f ≫ i₃ = i₁ ≫ f') (h2 : g ≫ i₃ = i₂ ≫ g') :
    pullback.map f g f' g' i₁ i₂ i₃ h1 h2 ≫ pullback.snd f' g' = pullback.snd f g ≫ i₂ :=
  pullback.lift_snd _ _ _

end GlobalTheory.Mum.FibEt

namespace GlobalTheory.Mum.FibEt

theorem exists_residue_factor {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) (s : S)
    (hs : π s = closedPoint R) :
    ∃ κ : ResidueField R →+* S.residueField s, S.fromSpecResidueField s ≫ π = spMap (κ.comp (residue R)) := by
  let φ := Spec.preimage (S.fromSpecResidueField s ≫ π)
  have hφ : Spec.map φ = S.fromSpecResidueField s ≫ π := Spec.map_preimage _
  have hpt : ∀ t : Spec (S.residueField s), (Spec.map φ) t = closedPoint R := by
    intro t
    rw [hφ, Scheme.Hom.comp_apply]
    have : S.fromSpecResidueField s t = s := by
      have := Set.mem_range_self (f := ⇑(S.fromSpecResidueField s)) t
      rwa [Scheme.range_fromSpecResidueField] at this
    rw [this, hs]
  have hker : ∀ r ∈ maximalIdeal R, φ.hom r = 0 := by
    intro r hr
    let t : Spec (S.residueField s) := closedPoint (S.residueField s)
    have h1 : (PrimeSpectrum.comap φ.hom t) = closedPoint R := hpt t
    have h2 : r ∈ (PrimeSpectrum.comap φ.hom t).asIdeal := by rw [h1]; exact hr
    simpa [t, closedPoint] using h2
  refine ⟨Ideal.Quotient.lift (maximalIdeal R) φ.hom hker, ?_⟩
  rw [← hφ]
  rfl

end GlobalTheory.Mum.FibEt

namespace GlobalTheory.Mum.FibEt

theorem smooth_affineSpace_sp (R : Type) [CommRing R] (g : ℕ) : Smooth (𝔸(Fin g; Sp R) ↘ Sp R) := by
  have e : (𝔸(Fin g; Sp R) ↘ Sp R) = (AffineSpace.isoOfIsAffine (Fin g) (Sp R)).hom ≫
      Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫ (Sp R).isoSpec.inv := by
    rw [← AffineSpace.isoOfIsAffine_inv_over (n := Fin g) (S := Sp R), Iso.hom_inv_id_assoc]
  rw [e]
  haveI : Algebra.Smooth Γ(Sp R, ⊤) (MvPolynomial (Fin g) Γ(Sp R, ⊤)) := ⟨inferInstance, inferInstance⟩
  have : Smooth (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := Γ(Sp R, ⊤)) (σ := Fin g)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  infer_instance

end GlobalTheory.Mum.FibEt


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mum.fibre_etale_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), a ≫ b = X.ι ≫ E.f → ∀ (x : P') (y : E.Y.left), E.j y = b x → (b ≫ PSpace.str R E.N) x = closedPoint R → ∀ (W0 : (PSpace R E.N).Opens) (g : ℕ) (τ0 : W0.toScheme ⟶ 𝔸(Fin g; Sp R)) (O : E.Y.left.Opens) (e : O.toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) (spMap (residue R))), y ∈ O → (O : Set E.Y.left) ⊆ E.j ⁻¹' W0 → τ0 ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = W0.ι ≫ PSpace.str R E.N → Etale e → e ≫ pullback.snd _ _ = O.ι ≫ E.Y.hom → (∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (w : T ⟶ W0.toScheme), w ≫ W0.ι = t ≫ O.ι ≫ E.j → t ≫ e ≫ pullback.fst _ _ = w ≫ τ0) → ∀ (c : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) M.π), c ≫ pullback.fst _ _ = (a ∣_ (b ⁻¹ᵁ W0)) ≫ (b ∣_ W0) ≫ τ0 → c ≫ pullback.snd _ _ = (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom → ∀ z : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme, ((a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ a) z = x → ∃ U : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme.Opens, z ∈ U ∧ Etale (U.ι ≫ c) := by
  intro R _ _ _ hR M G' _ _ hG E P' b X a hab x y hyb hx0 W0 g τ0 O e hyO hOW hτ0 he he2 he3 c hc1 hc2 z hz
  haveI : Smooth G'.hom := hG.smooth
  haveI : Smooth (𝔸(Fin g; Sp R) ↘ Sp R) := FibEt.smooth_affineSpace_sp R g
  haveI : Etale e := he
  let iV : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ G'.left := (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ X.ι ≫ E.H.ι
  let p : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ M.S := iV ≫ G'.hom
  have hh : c ≫ pullback.snd (𝔸(Fin g; Sp R) ↘ Sp R) M.π = p := by
    rw [hc2]; simp only [p, iV, Category.assoc]
  have hp : Smooth p := by dsimp only [p, iV]; infer_instance
  have key : a ≫ b ≫ PSpace.str R E.N = X.ι ≫ E.H.ι ≫ G'.hom ≫ M.π := by rw [reassoc_of% hab, E.f_over]
  have hs : M.π (p z) = closedPoint R := by
    have h1 := congrArg (fun f : X.toScheme ⟶ Sp R => f ((a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι z)) key
    simp only [Scheme.Hom.comp_apply] at h1 hz ⊢
    simp only [p, iV, Scheme.Hom.comp_apply]
    rw [← h1, hz]
    simpa [Scheme.Hom.comp_apply] using hx0
  obtain ⟨κ, hκ⟩ := FibEt.exists_residue_factor M.π (p z) hs
  obtain ⟨Ω', _, io, eG, l, -, hl1, hl2⟩ := E.fib (M.S.residueField (p z)) (M.S.fromSpecResidueField (p z)) κ hκ

  let Vs := (a ⁻¹ᵁ (b ⁻¹ᵁ W0))
  let x' : Sp Ω' ⟶ M.S := spMap io ≫ M.S.fromSpecResidueField (p z)
  let k' : Sp Ω' ⟶ Sp (ResidueField R) := spMap (io.comp κ)
  have hxk : x' ≫ M.π = k' ≫ spMap (residue R) := by
    simp only [x', k', Category.assoc, hκ, ← Spec.map_comp]; rfl
  have hpt : x' (closedPoint Ω') = p z := by
    simp only [x', Scheme.Hom.comp_apply]
    have := Set.mem_range_self (f := ⇑(M.S.fromSpecResidueField (p z))) ((spMap io) (closedPoint Ω'))
    rwa [Scheme.range_fromSpecResidueField] at this
  obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := x') z (closedPoint Ω') hpt.symm
  let mG : pullback p x' ⟶ pullback G'.hom x' :=
    pullback.map p x' G'.hom x' iV (𝟙 _) (𝟙 _) (by simp [p]) (by simp)
  let gm : pullback p x' ⟶ pullback E.Y.hom k' := mG ≫ eG.hom.left
  have hgms : gm ≫ pullback.snd E.Y.hom k' = pullback.snd p x' := by
    have hA : eG.hom.left ≫ pullback.snd E.Y.hom k' = pullback.snd G'.hom x' := Over.w eG.hom
    simp only [gm, Category.assoc, hA, mG, FibEt.map_snd', Category.comp_id]
  have E1 : mG ≫ l = pullback.fst p x' ≫ Vs.ι ≫ X.ι := by
    rw [← cancel_mono E.H.ι, Category.assoc, hl1]
    exact FibEt.map_fst' _ _ _ _ _ _ _ _ _
  have E2 : gm ≫ pullback.fst E.Y.hom k' ≫ E.j = pullback.fst p x' ≫ Vs.ι ≫ a ≫ b := by
    simp only [gm, Category.assoc]
    erw [← hl2]
    rw [reassoc_of% E1, hab]
  have hgmw : (gm ≫ pullback.fst E.Y.hom k') w = y := by
    haveI : IsImmersion E.j := E.imm
    apply E.j.isEmbedding.injective
    have h := congrArg (fun f : pullback p x' ⟶ PSpace R E.N => f w) E2
    simp only [Scheme.Hom.comp_apply] at h hz ⊢
    rw [h, hw1, hz, hyb]
  let Wo : (pullback p x').Opens := (gm ≫ pullback.fst E.Y.hom k') ⁻¹ᵁ O
  have hwW : w ∈ Wo := by
    show (gm ≫ pullback.fst E.Y.hom k') w ∈ O
    rw [hgmw]; exact hyO

  let A := 𝔸(Fin g; Sp R) ↘ Sp R
  let Oy := pullback (O.ι ≫ E.Y.hom) k'
  let eΩ : Oy ⟶ pullback (pullback.snd A (spMap (residue R))) k' :=
    pullback.map (O.ι ≫ E.Y.hom) k' (pullback.snd A (spMap (residue R))) k' e (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, he2]) (by simp)
  haveI : MorphismProperty.IsStableUnderComposition @Etale := MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have heΩ : Etale eΩ :=
    MorphismProperty.pullbackMap (P := @Etale) (f := O.ι ≫ E.Y.hom) (g := k') (f' := pullback.snd A (spMap (residue R)))
      (g' := k') (i₁ := e) (i₂ := 𝟙 _) he inferInstance he2.symm (by simp)
  let θ : pullback (pullback.snd A (spMap (residue R))) k' ⟶ pullback (pullback.snd A M.π) x' :=
    (pullbackLeftPullbackSndIso A (spMap (residue R)) k').hom ≫ (pullback.congrHom rfl hxk.symm).hom ≫
      (pullbackLeftPullbackSndIso A M.π x').inv
  have hθ1 : θ ≫ pullback.fst (pullback.snd A M.π) x' ≫ pullback.fst A M.π =
      pullback.fst (pullback.snd A (spMap (residue R))) k' ≫ pullback.fst A (spMap (residue R)) := by
    simp only [θ, Category.assoc, pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, FibEt.map_fst',
      Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
  have hθ2 : θ ≫ pullback.fst (pullback.snd A M.π) x' ≫ pullback.snd A M.π =
      pullback.snd (pullback.snd A (spMap (residue R))) k' ≫ x' := by
    simp only [θ, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd, pullback.congrHom_hom, FibEt.map_snd'_assoc,
      Category.id_comp]
    simp
  have hθ3 : θ ≫ pullback.snd (pullback.snd A M.π) x' = pullback.snd (pullback.snd A (spMap (residue R))) k' := by
    simp only [θ, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, FibEt.map_snd',
      Category.comp_id]
    simp

  let ψ : Wo.toScheme ⟶ Oy :=
    pullback.lift ((gm ≫ pullback.fst E.Y.hom k') ∣_ O) (Wo.ι ≫ gm ≫ pullback.snd E.Y.hom k') (by
      rw [← Category.assoc, morphismRestrict_ι]
      simp only [Category.assoc, pullback.condition]
      rfl)
  have hψ1 : ψ ≫ pullback.fst (O.ι ≫ E.Y.hom) k' = (gm ≫ pullback.fst E.Y.hom k') ∣_ O := pullback.lift_fst _ _ _
  have hψ2 : ψ ≫ pullback.snd (O.ι ≫ E.Y.hom) k' = Wo.ι ≫ gm ≫ pullback.snd E.Y.hom k' := pullback.lift_snd _ _ _
  let jO : Oy ⟶ pullback E.Y.hom k' :=
    pullback.map (O.ι ≫ E.Y.hom) k' E.Y.hom k' O.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  haveI : IsOpenImmersion jO :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (f := O.ι ≫ E.Y.hom) (g := k') (f' := E.Y.hom) (g' := k')
      (i₁ := O.ι) (i₂ := 𝟙 _) inferInstance inferInstance rfl (by simp)
  haveI : IsOpenImmersion mG :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (f := p) (g := x') (f' := G'.hom) (g' := x')
      (i₁ := iV) (i₂ := 𝟙 _) (by dsimp only [iV]; infer_instance) inferInstance rfl (by simp)
  haveI : IsIso eG.hom.left := by
    show IsIso ((Over.forget _).map eG.hom); infer_instance
  have hψj : ψ ≫ jO = Wo.ι ≫ gm := by
    apply pullback.hom_ext
    · dsimp only [jO]
      rw [Category.assoc, FibEt.map_fst', reassoc_of% hψ1, morphismRestrict_ι]
      simp only [Category.assoc]
      rfl
    · dsimp only [jO]
      rw [Category.assoc, FibEt.map_snd', Category.comp_id, hψ2]
      simp only [Category.assoc]
  haveI : IsOpenImmersion (ψ ≫ jO) := by rw [hψj]; dsimp only [gm]; infer_instance
  haveI : IsOpenImmersion ψ := IsOpenImmersion.of_comp ψ jO
  have hEq : Wo.ι ≫ pullback.map p x' (pullback.snd A M.π) x' c (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hh]) (by simp) = ψ ≫ eΩ ≫ θ := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · have hcond : (Wo.ι ≫ pullback.fst p x' ≫ (a ∣_ (b ⁻¹ᵁ W0)) ≫ (b ∣_ W0)) ≫ W0.ι =
            ((gm ≫ pullback.fst E.Y.hom k') ∣_ O) ≫ O.ι ≫ E.j := by
          simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc]
          rw [E2]
        simp only [Category.assoc]
        rw [hθ1, FibEt.map_fst'_assoc, hc1]
        dsimp only [eΩ]
        rw [FibEt.map_fst'_assoc, reassoc_of% hψ1, he3 _ _ _ hcond]
        simp only [Category.assoc]
      · simp only [Category.assoc]
        rw [hθ2, FibEt.map_fst'_assoc, hh]
        dsimp only [eΩ]
        rw [FibEt.map_snd'_assoc, Category.id_comp, reassoc_of% hψ2]
        rw [reassoc_of% hgms, pullback.condition]
    · simp only [Category.assoc]
      rw [hθ3, FibEt.map_snd', Category.comp_id]
      dsimp only [eΩ]
      rw [FibEt.map_snd', Category.comp_id, hψ2, hgms]
  have hEt : Etale (Wo.ι ≫ pullback.map p x' (pullback.snd A M.π) x' c (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hh]) (by simp)) := by
    rw [hEq]; infer_instance
  obtain ⟨U, hU, hUe⟩ := GlobalTheory.Mum.etale_near_of_etale_fibre M.S Vs.toScheme _ p (pullback.snd A M.π) c hh hp inferInstance Ω' x' Wo w hwW hEt
  exact ⟨U, hw1 ▸ hU, hUe⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedPolarisationKernelKilledSameIntegerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_polarisation_kernel_killed_same_integer : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (e : ℕ), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ (T : Over X) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1) → ∀ (T : Over Y) (x : T ⟶ A₀), (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | (exact @GlobalTheory.DescPolKer.pow_eq_one_of_descent) | (exact GlobalTheory.DescPolKer.pow_eq_one_of_descent) | (intros; apply GlobalTheory.DescPolKer.pow_eq_one_of_descent  <;> assumption)
end

