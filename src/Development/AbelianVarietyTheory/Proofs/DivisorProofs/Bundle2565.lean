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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2115
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleLogSectionNormProperties
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open scoped ContDiff

set_option autoImplicit false

namespace GlobalTheory.Mix.SecNorm

theorem logSec_basic : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (M : MLine p σ) (s : M.B.Sec), Measurable (M.logSec s) ∧ (∀ y : CxPts p σ, 0 < M.φ.nsq (secVal p σ s) y ↔ y ∈ ptsIn p σ (nonzeroLocus s)) ∧ (∀ y, CInfAt (M.φ.nsq (secVal p σ s)) y) ∧ ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), ∀ y ∈ ptsIn p σ (nonzeroLocus s), (M.addFn u hu).logSec s y = M.logSec s y - u y / 2 := by
  intro k _ X p σ M s
  have hpos : ∀ y : CxPts p σ, 0 < M.φ.nsq (secVal p σ s) y ↔ y ∈ ptsIn p σ (nonzeroLocus s) := fun y => by
    rw [← secVal_ne_zero_iff s (mem_pick M.φ.isLB y), Weight.nsq, mul_pos_iff_of_pos_right (Real.exp_pos _),
      sq_pos_iff, norm_ne_zero_iff]
  refine ⟨?_, hpos, fun y => ?_, fun u hu y hy => ?_⟩
  · exact (Real.measurable_log.comp (M.cInf.continuous_nsq s).measurable).div_const 2
  · have hi := mem_pick M.φ.isLB y
    have ho := (isOpen_ptsIn (p := p) (σ := σ) _).mem_nhds hi
    have h1 : CInfAt (fun z => ‖ev p σ (M.B.U (pick M.φ.isLB y)) (s.f _) z‖ ^ 2) y :=
      ⟨_, Unit, inferInstance, fun _ => s.f _, fun v => ‖v ()‖ ^ 2, univ, hi, isOpen_univ, trivial,
        ((contDiff_apply ℝ (fun _ => ℂ) ()).norm_sq ℂ).contDiffOn, EventuallyEq.rfl⟩
    refine (h1.comp₂ (M.cInf _ y hi) (G := fun x => x.1 * Real.exp (-x.2))
      (contDiff_fst.mul contDiff_snd.neg.exp)).congr ?_
    exact eventually_of_mem ho fun z hz => M.φ.nsq_eq (secVal_mem s) hz
  · have h := (hpos y).2 hy
    change Real.log ((M.φ.addFn u).nsq (secVal p σ s) y) / 2 = Real.log (M.φ.nsq (secVal p σ s) y) / 2 - u y / 2
    rw [Weight.nsq_addFn, Real.log_mul h.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring

end GlobalTheory.Mix.SecNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartSingleEquation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.PairStep

theorem exists_sncChart_isEqn_affine : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ (A : CartierDiv Y) (ι : Type) (s : ι → Y.functionField), (∀ i, s i ∈ A.sections) → ∀ y₀ : Y, ∃ (W : Y.Opens) (hW : y₀ ∈ W) (z : Fin n → Γ(Y, W)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ) (e : Y.functionFieldˣ) (f : ι → Γ(Y, W)), IsFrame (dOn q z) ∧ (∀ y ∈ W, A.IsEqn y e) ∧ (∀ i, fnOf W (gen_mem hW) (f i) = s i * e) ∧ ∀ (y : Y) (hy : y ∈ W), ∃ J : Finset (Fin n), IsSncChart q n B y W hy z J w u ∧ ∀ j ∈ J, y ∉ Y.basicOpen (z j) := by
  intro Y _ _ q n _ B hB A ι s hs y₀
  obtain ⟨U, hy₀, z, J, w, u, hc⟩ := GlobalTheory.T.exists_snc_chart ℂ Y q n B hB y₀
  have hgen : genericPoint Y ∉ B := GlobalTheory.PairStep.genericPoint_notMem_of_snc Y B hB
  obtain ⟨V, hyV, hV⟩ := _root_.GlobalTheory.PairStep.isSncChart_spread Y q n B y₀ U hy₀ z J w u hgen hc
  obtain ⟨N, hyN, e, he⟩ := A.exists_isEqn_nhds y₀
  obtain ⟨W, hWa, hyW, hWle⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (show y₀ ∈ U ⊓ V ⊓ N from ⟨⟨hy₀, hyV⟩, hyN⟩)
  have hWU : W ≤ U := hWle.trans (inf_le_left.trans inf_le_left)
  have hWV : W ≤ V := hWle.trans (inf_le_left.trans inf_le_right)
  have hWN : W ≤ N := hWle.trans inf_le_right
  have hf : ∀ i, ∃ a : Γ(Y, W), fnOf W (gen_mem hyW) a = s i * e := fun i =>
    exists_fnOf_eq (gen_mem hyW) fun x hx =>
      (he x (hWN hx)).regularAt_iff.1 (CartierDiv.mem_sections.1 (hs i) x)
  choose f hf using hf
  have hfr : IsFrame (dOn q fun j => resG Y hWU (z j)) := by
    have := hc.frame.res hWa hWU
    rwa [resForm_dOn] at this
  refine ⟨W, hyW, fun j => resG Y hWU (z j), w, u, e, f, hfr, fun y hy => he y (hWN hy), hf, ?_⟩
  intro y hy
  obtain ⟨hyU, J', -, hc', hJ'⟩ := hV y (hWV hy)
  refine ⟨J', ⟨hfr, ?_, hc'.spec, hc'.coheight, hc'.inj, hc'.ord_self, hc'.ord_other, hc'.mem⟩, ?_⟩
  · intro j hj
    rw [hc'.val j hj, fnOf_resG]
  · intro j hj hmem
    have hb : Y.basicOpen (resG Y hWU (z j)) = W ⊓ Y.basicOpen (z j) :=
      Y.basicOpen_res (z j) (homOfLE hWU).op
    rw [hb] at hmem
    exact hJ' j hj hmem.2

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncClosedEqIUnionClosureCodimOnePoints
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.SncGenericPoints

theorem mem_vanishingIdeal_closure {X : Scheme.{0}} (x : X) (U : X.affineOpens) (hx : x ∈ U.1)
    (s : Γ(X, U.1)) (hs : ¬ IsUnit (X.presheaf.germ U.1 x hx s)) :
    s ∈ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).ideal U := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  intro q hq
  by_contra hsq
  have hp : q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := by
    rw [U.2.fromSpec_preimage_basicOpen]; exact hsq
  have hq' : U.2.fromSpec q ∈ closure ({x} : Set X) := hq
  have hsp : x ⤳ U.2.fromSpec q := specializes_iff_mem_closure.2 hq'
  have hxs : x ∈ X.basicOpen s := hsp.mem_open (X.basicOpen s).isOpen hp
  exact hs ((X.mem_basicOpen s x hx).1 hxs)

theorem maximalIdeal_le_stalkId {X : Scheme.{0}} (x : X) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≤
      FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})) x := by
  intro a ha
  obtain ⟨V, hxV, f, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  have hle : W ≤ V := hWV
  have e : X.presheaf.germ W x hxW (X.presheaf.map (homOfLE hle).op f) = X.presheaf.germ V x hxV f :=
    X.presheaf.germ_res_apply (homOfLE hle) x hxW f
  rw [← e] at ha ⊢
  generalize X.presheaf.map (homOfLE hle).op f = g at ha ⊢
  have hu : ¬ IsUnit (X.presheaf.germ W x hxW g) :=
    mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 ha)
  have hm := mem_vanishingIdeal_closure x ⟨W, hW⟩ hxW g hu
  have h1 : Ideal.map (X.presheaf.germ W x hxW).hom
      ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).ideal ⟨W, hW⟩) ≤
      FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})) x :=
    le_iSup₂_of_le (f := fun (U : X.affineOpens) (hx : x ∈ U.1) =>
      Ideal.map (X.presheaf.germ U.1 x hx).hom
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).ideal U)) ⟨W, hW⟩ hxW le_rfl
  exact h1 (Ideal.mem_map_of_mem _ hm)

theorem coheight_eq_one_of_lSncAt {X : Scheme.{0}} {r : ℕ} (z : Fin r → X) (a : Fin r)
    (h : FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) (z a)) : Order.coheight (z a) = 1 := by
  obtain ⟨hreg, n, t, e, ht, hI⟩ := h
  have ha : z a ∈ (Closeds.closure {z a} : Closeds X) := subset_closure (Set.mem_singleton _)
  have hn : 1 ≤ n := (e ⟨a, ha⟩).pos
  have hm : IsLocalRing.maximalIdeal (X.presheaf.stalk (z a)) = Ideal.span {t (e ⟨a, ha⟩)} := by
    refine le_antisymm ((maximalIdeal_le_stalkId (z a)).trans (hI ⟨a, ha⟩).le) ?_
    rw [← ht.1]
    exact Ideal.span_mono (Set.singleton_subset_iff.2 ⟨_, rfl⟩)
  have hmin : IsLocalRing.maximalIdeal (X.presheaf.stalk (z a)) ∈
      (Ideal.span {t (e ⟨a, ha⟩)}).minimalPrimes := by
    rw [← hm, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have h1 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := X.presheaf.stalk (z a))
  have h2 := ringKrullDim_stalk_eq_coheight (z a)
  have h3 : (IsLocalRing.maximalIdeal (X.presheaf.stalk (z a))).height = Order.coheight (z a) :=
    WithBot.coe_eq_coe.1 (h1.trans h2)
  have h4 : ((n : ℕ∞)) = Order.coheight (z a) := WithBot.coe_eq_coe.1 (ht.2.trans h2)
  refine le_antisymm (h3 ▸ hle) ?_
  rw [← h4]
  exact_mod_cast hn

theorem exists_genericPoints : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ T : Closeds X, FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T) → ∃ (r : ℕ) (z : Fin r → X), Function.Injective z ∧ (∀ a, Order.coheight (z a) = 1) ∧ (T : Set X) = ⋃ a, closure {z a} ∧ (∀ w : X, w ∈ T → Order.coheight w = 1 → ∃ a, w = z a) ∧ ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x := by
  intro F _ X _ p D hp hs T hT
  haveI : QuasiCompact p := by
    obtain ⟨N, i, hi, rfl⟩ := hp
    haveI : IsProper (PSpace.str F N) := isProper_str F N
    infer_instance
  haveI : Smooth p := SmoothOfRelativeDimension.smooth D p
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian X := {}
  obtain ⟨m, C, hC, -⟩ := GlobalTheory.SncComponents.exists_compList_effCartier F X p D T hT
  have hL := GlobalTheory.SncLocal.lSncAt_of_snc' X T m C hT hC
  have hz : ∀ a, ∃ z : X, closure {z} = (C a : Set X) := fun a =>
    QuasiSober.sober (hC.1 a) (C a).isClosed
  choose z hz using hz
  have hCz : (fun a => (Closeds.closure {z a} : Closeds X)) = C :=
    funext fun a => SetLike.coe_injective (hz a)
  have hL' : ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x := by
    rw [hCz]; exact hL
  have hco : ∀ a, Order.coheight (z a) = 1 := fun a => coheight_eq_one_of_lSncAt z a (hL' _)
  have hU : (T : Set X) = ⋃ a, closure {z a} := by
    rw [← hC.2.1]; simp only [hz]
  refine ⟨m, z, fun a b hab => hC.2.2 a b ?_, hco, hU, fun w hw hw1 => ?_, hL'⟩
  · rw [← hz, ← hz, hab]
  · have hw' : w ∈ (T : Set X) := hw
    rw [hU] at hw'
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hw'
    have hsp : z a ⤳ w := specializes_iff_mem_closure.2 ha
    refine ⟨a, ?_⟩
    by_contra hne
    have hlt : w < z a := lt_of_le_not_ge hsp fun h =>
      hne ((show w ⤳ z a from h).antisymm hsp).eq
    have := Order.coheight_strictAnti hlt (by rw [hco a]; exact ENat.natCast_lt_top 1)
    rw [hco a, hw1] at this
    exact lt_irrefl _ this

end GlobalTheory.SncGenericPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapCompEqOfCompInjectiveLocalScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
namespace GlobalTheory.TInj

theorem spMap_comp_eq_of_injective {Y : Scheme.{0}} {W R' V : Type} [CommRing W] [IsLocalRing W]
    [CommRing R'] [CommRing V] (u : Sp W ⟶ Y) (g₁ g₂ : W →+* R') (η' : R' →+* V)
    (hη : Function.Injective η')
    (h : spMap (η'.comp g₁) ≫ u = spMap (η'.comp g₂) ≫ u) :
    spMap g₁ ≫ u = spMap g₂ ≫ u := by
  have hu := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of W) u
  have key : ∀ g : W →+* R', spMap g ≫ u =
      Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of W) u ≫ CommRingCat.ofHom g) ≫
        Y.fromSpecStalk (u (closedPoint (CommRingCat.of W))) := by
    intro g
    conv_lhs => rw [← hu]
    simp only [spMap, Spec.map_comp, Category.assoc]
  have key' : ∀ g : W →+* R', spMap (η'.comp g) ≫ u =
      Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of W) u ≫ CommRingCat.ofHom g ≫
        CommRingCat.ofHom η') ≫ Y.fromSpecStalk (u (closedPoint (CommRingCat.of W))) := by
    intro g
    conv_lhs => rw [← hu]
    simp only [spMap, Spec.map_comp, Category.assoc, CommRingCat.ofHom_comp]
  rw [key', key'] at h
  have h2 := (cancel_mono _).1 h
  have h3 := Spec.map_injective h2
  have h4 : Scheme.stalkClosedPointTo (R := CommRingCat.of W) u ≫ CommRingCat.ofHom g₁ =
      Scheme.stalkClosedPointTo (R := CommRingCat.of W) u ≫ CommRingCat.ofHom g₂ := by
    ext a
    apply hη
    have := congrArg (fun f => f.hom a) h3
    simpa using this
  rw [key, key, h4]

end GlobalTheory.TInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusPartGenericFibreClosedFibreDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibClosed

open GlobalTheory.SplitTorus (torusMap bcMap bcIso)

section General

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left} {X : Type} [AddCommGroup X]

theorem pullTorus_left_comp_iso (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G) :
    (pullTorus h i).left ≫ h.1.isoPullback.hom = (bcIso f X).hom.left ≫ ((Over.pullback f).map i).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, IsPullback.isoPullback_hom_fst, pullTorus_left, Category.assoc]
    have : ((Over.pullback f).map i).left ≫ pullback.fst G.hom f = pullback.fst (splitTorus S X).hom f ≫ i.left := by
      simp
    rw [this, ← Category.assoc, GlobalTheory.SplitTorus.bcIso_hom_fst]
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd, Category.assoc]
    have : ((Over.pullback f).map i).left ≫ pullback.snd G.hom f = pullback.snd (splitTorus S X).hom f := by
      simp
    rw [this, Over.w (pullTorus h i)]
    exact (Over.w (bcIso f X).hom).symm

theorem mono_pullTorus (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G)
    (hc : IsClosedImmersion ((Over.pullback f).map i).left) : Mono (pullTorus h i) := by
  have k := pullTorus_left_comp_iso h i
  have : Mono ((bcIso f X).hom.left ≫ ((Over.pullback f).map i).left) := inferInstance
  rw [← k] at this
  have : Mono (pullTorus h i).left := mono_of_mono _ h.1.isoPullback.hom
  exact (Over.forget _).mono_of_mono_map this

theorem closedImm_of_pullTorus (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G)
    (hc : IsClosedImmersion (pullTorus h i).left) : IsClosedImmersion ((Over.pullback f).map i).left := by
  have k := pullTorus_left_comp_iso h i
  have e : ((Over.pullback f).map i).left = (bcIso f X).inv.left ≫ (pullTorus h i).left ≫ h.1.isoPullback.hom := by
    rw [k, ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
  haveI : IsIso (bcIso f X).inv.left := inferInstanceAs (IsIso ((Over.forget _).map (bcIso f X).inv))
  rw [e]
  infer_instance

theorem isClosedImmersion_of_isTorPart {tι : splitTorus S X ⟶ G} (h : IsTorPart tι) : IsClosedImmersion tι.left := by
  obtain ⟨-, B, _, q, hB, -, hk⟩ := h
  have h₁ : IsClosedImmersion (η[B].left ≫ B.hom) := by
    rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
  have h₂ : IsClosedImmersion η[B].left := IsClosedImmersion.of_comp _ B.hom
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hk.map (Over.forget S)).flip h₂

theorem isIso_torusMap (T : Scheme.{0}) {Y : Type} [AddCommGroup Y] (e : X ≃+ Y) :
    IsIso (torusMap T e.toAddMonoidHom) :=
  ⟨torusMap T e.symm.toAddMonoidHom, by
    rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_id]; congr 1; ext x; simp, by
    rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_id]; congr 1; ext x; simp⟩

end General

theorem spMap_fractionRing_closedPoint (V : Type) [CommRing V] [IsDomain V] :
    (spMap (algebraMap V (FractionRing V))) (closedPoint (FractionRing V)) = genericPoint (Sp V) := by
  rw [genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap V (FractionRing V)) (maximalIdeal (FractionRing V)) = ⊥
  rw [maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V _)

theorem bijective_of_mono_torusMap {κ : Type} [Field κ] {X₀ X₁ : Type} [AddCommGroup X₀] [AddCommGroup X₁]
    [Module.Free ℤ X₀] [Module.Finite ℤ X₀] [Module.Free ℤ X₁] [Module.Finite ℤ X₁]
    (hr : Module.finrank ℤ X₀ = Module.finrank ℤ X₁) (ρ : X₀ →+ X₁) [Mono (torusMap (Sp κ) ρ)] :
    Function.Bijective ρ := by
  have hs : Function.Surjective ρ := by
    let l : X₁ →+ X₁ ⧸ ρ.range := QuotientAddGroup.mk' ρ.range
    have e : torusMap (Sp κ) l ≫ torusMap (Sp κ) ρ =
        torusMap (Sp κ) (0 : X₁ →+ X₁ ⧸ ρ.range) ≫ torusMap (Sp κ) ρ := by
      rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp]
      congr 1
      ext x
      simp [l]
    have e2 := GlobalTheory.SplitTorus.torusMap_injective ((cancel_mono _).1 e)
    intro y
    have hy : QuotientAddGroup.mk' ρ.range y = 0 := DFunLike.congr_fun e2 y
    obtain ⟨x, hx⟩ := (QuotientAddGroup.eq_zero_iff y).1 hy
    exact ⟨x, hx⟩
  let e₀ : X₁ ≃ₗ[ℤ] X₀ := LinearEquiv.ofFinrankEq X₁ X₀ hr.symm
  have hinj := OrzechProperty.injective_of_surjective_endomorphism (e₀.toLinearMap ∘ₗ ρ.toIntLinearMap)
    (e₀.surjective.comp hs)
  exact ⟨fun a b hab => hinj (by simp [hab]), hs⟩

end GlobalTheory.Poinc.FibClosed

namespace GlobalTheory.Poinc.FibClosed

open GlobalTheory.SplitTorus (torusMap bcMap bcIso)

theorem isTorPart_pullTorus_closed : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (X₁ : Type) [AddCommGroup X₁] [Module.Free ℤ X₁] [Module.Finite ℤ X₁] (j : splitTorus (Sp V) X₁ ⟶ G₁), IsMonHom j → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), IsTorPart (pullTorus hψ j) → ∀ (κ : Type) [Field κ] (b : V →+* κ), IsLocalHom b → ∀ (G₀ : Over (Sp κ)) [GrpObj G₀] (ψ₀ : G₀.left ⟶ G₁.left) (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀) (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (t₀ : splitTorus (Sp κ) X₀ ⟶ G₀), IsTorPart t₀ → Module.finrank ℤ X₀ = Module.finrank ℤ X₁ → IsTorPart (pullTorus hψ₀ j) := by
  intro V _ _ _ G₁ _ _ hG X₁ _ _ _ j hj GK _ ψ hψ hgen κ _ b hb G₀ _ ψ₀ hψ₀ X₀ _ _ _ t₀ ht₀ hr
  haveI := hj
  let e : X₁ ≃+ (Fin (Module.finrank ℤ X₁) → ℤ) := (Module.finBasis ℤ X₁).equivFun.toAddEquiv
  let u : splitTorus (Sp V) (Fin (Module.finrank ℤ X₁) → ℤ) ⟶ G₁ := torusMap (Sp V) e.toAddMonoidHom ≫ j
  have hu : IsMonHom u := inferInstance
  have hgenU : ∀ (k : Type) [Field k] (g : Sp k ⟶ Sp V), g (closedPoint k) = genericPoint (Sp V) →
      IsClosedImmersion ((Over.pullback g).map u).left := by
    intro k _ g hg
    rw [GlobalTheory.TorusFibreImm.closedImm_iff_residue u k g, hg, ← spMap_fractionRing_closedPoint V,
      ← GlobalTheory.TorusFibreImm.closedImm_iff_residue u (FractionRing V) _]
    refine closedImm_of_pullTorus hψ u ?_
    rw [pullTorus_torusMap_comp, Over.comp_left]
    haveI := isClosedImmersion_of_isTorPart hgen
    haveI := isIso_torusMap (Sp (FractionRing V)) e
    haveI : IsIso (torusMap (Sp (FractionRing V)) e.toAddMonoidHom).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (torusMap (Sp (FractionRing V)) e.toAddMonoidHom)))
    infer_instance
  have hsp := GlobalTheory.TorusFibre.isClosedImmersion_special_of_local V (FractionRing V) G₁ hG _ u hu
    (by
      haveI := hgenU (FractionRing V) _ (spMap_fractionRing_closedPoint V)
      exact (Over.forget _).mono_of_mono_map
        (inferInstanceAs (Mono ((Over.pullback (spMap (algebraMap V (FractionRing V)))).map u).left)))
  have hfib : IsClosedImmersion ((Over.pullback (spMap b)).map u).left := by
    have h2 := (GlobalTheory.TorusFibreImm.closedImm_iff_residue u (ResidueField V) _).1 hsp
    have h3 : (Spec.map (CommRingCat.ofHom (algebraMap V (ResidueField V)))) (closedPoint (ResidueField V)) =
        (spMap b) (closedPoint κ) :=
      (IsLocalRing.comap_closedPoint (residue V)).trans (IsLocalRing.comap_closedPoint b).symm
    rw [GlobalTheory.TorusFibreImm.closedImm_iff_residue, ← h3]
    exact h2
  have hmono : Mono (pullTorus hψ₀ u) := mono_pullTorus hψ₀ u hfib
  have hmono' : Mono (pullTorus hψ₀ j) := by
    have k : pullTorus hψ₀ j = torusMap _ e.symm.toAddMonoidHom ≫ pullTorus hψ₀ u := by
      rw [pullTorus_torusMap_comp, ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp,
        show e.symm.toAddMonoidHom.comp e.toAddMonoidHom = AddMonoidHom.id X₁ from by ext x; simp,
        GlobalTheory.SplitTorus.torusMap_id, Category.id_comp]
    haveI := isIso_torusMap (Sp κ) e.symm
    rw [k]
    infer_instance
  obtain ⟨ρ, hρ⟩ := ht₀.factor (pullTorus hψ₀ j) inferInstance
  haveI : Mono (torusMap (Sp κ) ρ) := by
    rw [hρ] at hmono'
    exact mono_of_mono _ t₀
  have hbij := bijective_of_mono_torusMap (κ := κ) hr ρ
  have h := ht₀.equiv (AddEquiv.ofBijective ρ hbij)
  rw [hρ]
  exact h

end GlobalTheory.Poinc.FibClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupSymmetricLiftActionFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

namespace GlobalTheory.Mum.Desc

theorem isActOf_secExt : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), Odd N → ∀ (x : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))) (θ' : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → SymLift A.A A.L N N (baseEm em ≫ x) θ' → ∀ t t' : SecF A (Kb R) N, IsActOf A.A A.L N θ t t' → IsActOf A.A A.L N θ' (secExt A em N t) (secExt A em N t') := by
  intro R _ _ A F _ _ em N hN x θ θ' H H' t t' a
  exact GlobalTheory.WeightProbe.act_pull A hN (baseEm em) H H' a

end GlobalTheory.Mum.Desc
end

