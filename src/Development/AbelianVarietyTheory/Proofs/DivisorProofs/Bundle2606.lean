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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2538
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2543
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableLogNormSectionMixedChernForms
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory Metric
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixLogSec

theorem exists_integrableOn {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {D : ℕ} [SecondCountableTopology (CxPts p σ)] (hσ : Function.Injective σ) (L : Fin D → MLine p σ)
    (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (ε : ℤˣ) (c : AlgChart p σ D)
    {y : CxPts p σ} (hy : y ∈ c.e.source) :
    ∃ O ∈ 𝓝 y, IntegrableOn (M.logSec s) (ptsIn p σ (nonzeroLocus s) ∩ O) (part L ε) := by
  have : IsDomain k := hσ.isDomain σ
  set i := pick M.φ.isLB y
  have hi : y ∈ ptsIn p σ (M.B.U i) := mem_pick _ y
  have hT' := (isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (M.B.U i))).mem_nhds (mem_over c.e hy hi)
  have hd : ∀ᶠ v in 𝓝 (c.e y), DifferentiableAt ℂ (ev p σ _ (s.f i) ∘ c.e.symm) v :=
    (c.holo _ _).eventually_differentiableAt hT'
  have hfr : ∃ᶠ v in 𝓝 (c.e y), (ev p σ _ (s.f i) ∘ c.e.symm) v ≠ 0 := by
    have h := Measure.dense_of_ae (SemiPosBir.ae_mem hσ c (U := nonzeroLocus s) ⟨_, hs⟩)
    have h₁ := mem_closure_iff_frequently.1 (h (c.e y))
    refine (h₁.and_eventually hT').mono ?_
    rintro v ⟨h₂, h₃⟩
    exact (secVal_ne_zero_iff s h₃.2).2 (h₂ h₃.1)
  obtain ⟨δ, hδ, -, hint⟩ := exists_integrableOn_log_norm_of_frequently_ne_zero volume hd hfr
  obtain ⟨η, hη, hηs⟩ := nhds_basis_closedBall.mem_iff.1 (inter_mem hT' (ball_mem_nhds _ hδ))
  have hcont : ContinuousOn (fun v => dens L c (c.e.symm v)) c.e.target :=
    (_root_.GlobalTheory.Mix.continuousOn_dens k X p σ D L c).comp c.e.continuousOn_symm c.e.mapsTo_symm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (c.e y) η).exists_bound_of_continuousOn
    (hcont.mono fun v hv => (hηs hv).1.1)
  set O := c.e.source ∩ c.e ⁻¹' ball (c.e y) η
  have hO : IsOpen O := c.e.continuousOn.isOpen_inter_preimage c.e.open_source isOpen_ball
  set S := ptsIn p σ (nonzeroLocus s) ∩ O
  have hS : IsOpen S := (isOpen_ptsIn _).inter hO
  have hSs : S ⊆ c.e.source := fun z hz => hz.2.1
  have him : c.e '' S ⊆ closedBall (c.e y) η := by
    rintro _ ⟨z, hz, rfl⟩
    exact ball_subset_closedBall hz.2.2
  have hSi (z) (hz : z ∈ S) : z ∈ ptsIn p σ (M.B.U i) := by
    have := (hηs (him (mem_image_of_mem _ hz))).1.2
    rwa [mem_preimage, c.e.left_inv (hSs hz)] at this
  have hne (z) (hz : z ∈ S) : ev p σ _ (s.f i) z ≠ 0 := (secVal_ne_zero_iff s (hSi z hz)).2 hz.1
  have heq (z) (hz : z ∈ S) : M.logSec s z = Real.log ‖ev p σ _ (s.f i) z‖ - M.φ.φ i z / 2 := by
    rw [MLine.logSec, M.φ.nsq_eq (secVal_mem s) (hSi z hz), secVal_apply,
      Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (hne z hz))) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
    push_cast
    ring
  have hm := measurableSet_image c.e hS.measurableSet hSs
  refine ⟨O, hO.mem_nhds ⟨hy, by exact Set.mem_preimage.mpr (mem_ball_self hη)⟩, LogNormInt.integrableOn_of_chart c.e
    (fun A hA hAs => _root_.GlobalTheory.Mix.part_apply k X p σ D L ε c A hA hAs) hS.measurableSet hSs
    (C := ENNReal.ofReal C) ENNReal.ofReal_ne_top (fun v hv => ENNReal.ofReal_le_ofReal ?_) ?_ ?_⟩
  · have h := hC v (him hv)
    rw [Real.norm_eq_abs, abs_le] at h
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simpa using h.2
    · simpa [neg_le] using h.1
  · refine ContinuousOn.congr (fun z hz => ContinuousAt.continuousWithinAt ?_) heq
    exact ((((continuousOn_ev (s.f i)).continuousAt ((isOpen_ptsIn _).mem_nhds (hSi z hz))).norm.log
      (norm_ne_zero_iff.2 (hne z hz))).sub ((M.cInf i z (hSi z hz)).continuousAt.div_const 2))
  · have hsub : c.e '' S ⊆ ball (c.e y) δ := fun v hv => (hηs (him hv)).2
    have h₁ : IntegrableOn (fun v => (M.φ.φ i ∘ c.e.symm) v / 2) (c.e '' S) :=
      (((((contDiffOn_chart (M.cInf i) c).continuousOn.mono fun v hv => (hηs hv).1).div_const
        2).integrableOn_compact (isCompact_closedBall _ _)).mono_set him)
    refine ((hint.mono_set hsub).sub h₁).congr ?_
    filter_upwards [ae_restrict_mem hm] with v hv'
    obtain ⟨z, hz, rfl⟩ := hv'
    simp only [Function.comp_apply, Pi.sub_apply, c.e.left_inv (hSs hz)]
    exact (heq z hz).symm

theorem intg_logSec : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ (L : Fin D → MLine p σ) (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → Intg L (M.logSec s) := by
  intro F _ X _ _ p σ D hp hsm L M s hs
  have := CxPts.compactSpace σ hp
  have := CxPts.secondCountableTopology_of_isProjOver σ hp
  have key (ε : ℤˣ) : Integrable (M.logSec s) (part L ε) := by
    have h (y : CxPts p σ) : ∃ O ∈ 𝓝 y, IntegrableOn (M.logSec s) (ptsIn p σ (nonzeroLocus s) ∩ O) (part L ε) :=
      have ⟨c, hc⟩ := AlgChart.exists_mem_source (D := D) y
      exists_integrableOn σ.injective L M s hs ε c hc
    choose O hO hint using h
    obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover O fun y _ => hO y
    have h₁ : IntegrableOn (M.logSec s) (ptsIn p σ (nonzeroLocus s)) (part L ε) := by
      refine ((integrableOn_finset_iUnion (s := t)).2 fun y _ => hint y).mono_set fun z hz => ?_
      obtain ⟨y, hy, hz'⟩ := mem_iUnion₂.1 (ht (mem_univ z))
      exact mem_iUnion₂.2 ⟨y, hy, hz, hz'⟩
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (s := ptsIn p σ (nonzeroLocus s))
      (mem_ae_iff.2 (_root_.GlobalTheory.MixNull.part_compl_null F X p σ σ.injective hp D L ε _ hs))] at h₁
  exact ⟨key 1, key (-1)⟩

end GlobalTheory.MixLogSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureFiniteEtaleOriginKeyLemmaEssFinit
section
open IsLocalRing Polynomial
open scoped TensorProduct

theorem GlobalTheory.GoodEtale.closure_finiteEtale : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (ρ : Localization.AtPrime QA →+* A), ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A →
      RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} →
    ∀ (q : ℕ), 0 < q → IsUnit (q : A) →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
      GlobalTheory.KeyOriginNoeth.Good A (Localization.AtPrime QA) DA ρ →
      GlobalTheory.KeyOriginNoeth.ClosureFiniteEtale A (Localization.AtPrime QA) DA := by
  intro A _ _ _ _ _ _ EA _ _ _ _ _ QA _ hQA ρ hρ hker q hq hqu DA _ _ actA htor hgood
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨hflat, hnoeth, ht, hic⟩ := GlobalTheory.T.genericFibreBase_flat_noetherian_intClosed A EA QA hQA ρ hρ hker
  haveI := hflat
  haveI := hnoeth
  have hHR := GlobalTheory.T.hasHartogsPropertyHeightOnePrimes_of_flat A (Localization.AtPrime QA)
  obtain ⟨act', T, hT, ⟨a, ha, n, x, y, hxy⟩, htf, hHC, hint, hnt⟩ :=
    GlobalTheory.T.integralClosure_zmodTorsor_genericFibre_data A (Localization.AtPrime QA) hHR hic q DA actA htor
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A (Localization.AtPrime QA) DA
  obtain ⟨hEt, s, hs⟩ := hgood
  obtain ⟨O, _, _, hO, hσ⟩ := GlobalTheory.T.exists_faithfullyFlat_algHom_etale_height_one A (Localization.AtPrime QA) (GlobalTheory.KeyOriginNoeth.closure A _ DA)
    ρ hρ _ hker ht hint (fun P _ h => hEt P h) ⟨s, hs⟩
  obtain ⟨hfin, het⟩ := GlobalTheory.T.finiteEtale_of_galois_descent_hartogs A (Localization.AtPrime QA) (GlobalTheory.KeyOriginNoeth.closure A _ DA) O
    (Multiplicative (ZMod q)) act' T hT a ha n x y hxy htf hHC (fun P _ h => hEt P h) hσ
  exact ⟨hfin, het, hnt⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCombinationTermsRationalPointFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntEval
open GlobalTheory.UT.CoefBasic GlobalTheory.ExpansionValueZero GlobalTheory.BoxExpansion

theorem coef_comb_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (g : GtPt D (𝟙_ (Over (Sp R)))) (g' : GtPtF D (FractionRing R)), GtPt.IsPullF (FractionRing R) (toUnit (TF (R := R) (FractionRing R))).left g g' → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, g.b.left] (DegPre.lineε 1))) (l : FractionRing R), l ≠ 0 → ∀ (k : ℕ) (wk : Frm D (FractionRing R) k g'.b), wk.IsGen → (∀ (z : (TF (R := R) (FractionRing R)).left) (J : ((TF (R := R) (FractionRing R)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing R) z (l ^ k) * (val wk (𝟙 _) z J).val = (val t (toUnit (TF (R := R) (FractionRing R))).left z J ^ k).val) → ∀ (s : Fam D (FractionRing R) k) (n : ℕ) (c : Fin n → FractionRing R) (fs : Fin n → ∀ α : D.X, D.SecB k α), (∀ α : D.X, GeneratorPullback.SecLin D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (fun i => fs i α) (DegPre.prB D (FractionRing R)).left (fun i => scal (fst (TF (R := R) (FractionRing R)) D.P.A).left (c i))) → ∀ a : Fin n → D.X → R, (∀ (i : Fin n) (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → sval (fs i α) (r ≫ g.b.left) z J * (val (g.s α) r z J).val * (val t r z J ^ k).val = Geo.Tor.cst r z (a i α) * (val (L := D.P.L) D.rig r z J ^ k).val) → ∀ α : D.X, l ^ k * coef s g' wk α = ∑ i, c i * algebraMap R (FractionRing R) (a i α) := by
  intro R _ _ D g g' hP t l hl k wk hwk hl' s n c fs hs a ha α
  have hτ : (toUnit (TF (R := R) (FractionRing R))).left = jFK (R := R) (FractionRing R) ≫ jK R := by
    have := Over.w (toUnit (TF (R := R) (FractionRing R)))
    simpa using this
  have hb : g'.b.left = (toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left := hP.1
  have hlk : (l ^ k) ≠ 0 := pow_ne_zero _ hl
  suffices key : IsCoef k g' wk α (s.s α) ((l ^ k)⁻¹ * ∑ i, c i * algebraMap R (FractionRing R) (a i α)) by
    rw [coef_eq key, ← _root_.mul_assoc, mul_inv_cancel₀ hlk, _root_.one_mul]
  intro z J hJ
  have e₂ : (lift (𝟙 (TF (R := R) (FractionRing R))) g'.b).left ≫ (DegPre.prB D (FractionRing R)).left =
      (toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left := by
    rw [← Over.comp_left]
    erw [lift_snd]
    exact hb
  have e₃ : (lift (𝟙 (TF (R := R) (FractionRing R))) g'.b).left ≫ (fst (TF (R := R) (FractionRing R)) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have v : val (g'.s α) (𝟙 _) z J = val (g.s α) (toUnit (TF (R := R) (FractionRing R))).left z J := by
    rw [val_corr hJ (hP.2 α), val_pull hJ, Category.id_comp]
  have bi : ∀ i, gs (lift (𝟙 (TF (R := R) (FractionRing R))) g'.b).left z ⊤
      (scal (fst (TF (R := R) (FractionRing R)) D.P.A).left (c i)) = cstH z (c i) := fun i =>
    ((gs_pull _ _ z ⊤ trivial _).trans (by rw [e₃]; rfl)).trans (cst_eq z _)
  have hai : ∀ i, sval (fs i α) ((toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left) z J *
      (val (g.s α) (toUnit (TF (R := R) (FractionRing R))).left z J).val *
      (val t (toUnit (TF (R := R) (FractionRing R))).left z J ^ k).val =
      cstH z (algebraMap R (FractionRing R) (a i α)) *
        (val (L := D.P.L) D.rig (toUnit (TF (R := R) (FractionRing R))).left z J ^ k).val := fun i => by
    rw [ha i α _ _ z J hJ]
    congr 1
    rw [hτ, GlobalTheory.UT.EvalZero.cst_base]
    simp
  have hr : rigV D (TF (R := R) (FractionRing R)).hom z J =
      val (L := D.P.L) D.rig (toUnit (TF (R := R) (FractionRing R))).left z J := by
    rw [hτ]; rfl
  have hw := hl' z J hJ
  rw [cst_eq] at hw ⊢
  refine ((IsUnit.mk0 _ hlk).map (cstH (R := R) z)).mul_left_cancel ?_
  rw [secLin_val (hs α) _ z hJ, e₂, v, hr]
  simp only [bi]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← _root_.mul_assoc, ← map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ hlk, _root_.one_mul, map_sum,
    Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := hai i
  have h2 := hw
  simp only [Units.val_pow_eq_pow_val, map_mul] at h1 h2 ⊢
  linear_combination (-(cstH (R := R) z (c i))) * h1 - cstH (R := R) z (c i) *
    sval (fs i α) ((toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left) z J *
    (val (g.s α) (toUnit (TF (R := R) (FractionRing R))).left z J).val * h2

end GlobalTheory.Poinc.IntEval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAnalyticSNCOfAlgebraicSNCSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecSnc

open GlobalTheory.ShFam (LiesIn ev_eq_zero_iff isOpen_not_liesIn)

section Local

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem eventually_ev_eq (x : CxPts p σ) {U V : X.Opens} (hU : x.1 (IsLocalRing.closedPoint ℂ) ∈ U)
    (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V) (f : Γ(X, U)) (g : Γ(X, V))
    (h : X.presheaf.germ U _ hU f = X.presheaf.germ V _ hV g) :
    ∀ᶠ y in 𝓝 x, ev p σ U f y = ev p σ V g y := by
  obtain ⟨W, hW, iU, iV, he⟩ := TopCat.Presheaf.germ_eq X.presheaf _ hU hV f g h
  have hWU : W ≤ U := leOfHom iU
  have hWV : W ≤ V := leOfHom iV
  have hres : resG X hWU f = resG X hWV g := he
  refine Filter.eventually_of_mem ((isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)) fun z hz => ?_
  rw [← ev_res hWU hz, ← ev_res hWV hz, hres]

theorem eventually_ev_ne_zero (x : CxPts p σ) {V : X.Opens} (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V)
    (g : Γ(X, V)) (h : IsUnit (X.presheaf.germ V _ hV g)) : ∀ᶠ y in 𝓝 x, ev p σ V g y ≠ 0 := by
  have hx : x ∈ ptsIn p σ (X.basicOpen g) := mem_ptsIn.2 ((X.mem_basicOpen g _ hV).2 h)
  refine Filter.eventually_of_mem ((isOpen_ptsIn _).mem_nhds hx) fun z hz => ?_
  exact (mem_ptsIn_basicOpen (ptsIn_mono (X.basicOpen_le g) hz) g).1 hz

theorem eventually_ev_eq_zero_iff [IsLocallyNoetherian X] (x : CxPts p σ) (V : X.affineOpens)
    (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V.1) (g : Γ(X, V.1)) (C : Closeds X)
    (h : FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal C) (x.1 (IsLocalRing.closedPoint ℂ)) =
      Ideal.span {X.presheaf.germ V.1 _ hV g}) :
    ∀ᶠ y in 𝓝 x, (ev p σ V.1 g y = 0 ↔ LiesIn y C) := by
  rw [WMult.stalkId_eq_map_germ _ _ V hV] at h
  obtain ⟨s, hs, H⟩ := GlobalTheory.IdealSpread.ideal_eq_span_of_germ X _ V _ hV g
    (IsLocallyNoetherian.component_noetherian V) h
  refine Filter.eventually_of_mem ((isOpen_ptsIn _).mem_nhds (mem_ptsIn.2 hs)) fun z hz => ?_
  rw [← ev_res (X.basicOpen_le s) hz]
  exact ev_eq_zero_iff (V := X.affineBasicOpen s) (H s le_rfl) hz

theorem mem_range_ptMap_closι (z : X) (y : CxPts p σ) :
    y ∈ Set.range (ptMap (closι z) rfl σ) ↔ LiesIn y (Closeds.closure {z}) := by
  have hr : Set.range (closι z) = (Closeds.closure {z} : Closeds X) :=
    (Scheme.IdealSheafData.range_subschemeι _).trans (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  constructor
  · rintro ⟨w, rfl⟩
    have : closι z (w.1 (IsLocalRing.closedPoint ℂ)) ∈ Set.range (closι z) := ⟨_, rfl⟩
    rw [hr] at this
    exact this
  · intro hy
    have : IsReduced (Sp ℂ) := inferInstanceAs (IsReduced (Spec _))
    have hle : Set.range y.1 ⊆ Set.range (closι z) := by
      rintro _ ⟨a, rfl⟩
      have ha : a = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
      rw [hr, ha]
      exact hy
    have hk : (closι z).ker ≤ y.1.ker := ker_le_ker_of_range_subset_of_isReduced (closι z) y.1 hle
    have hl := IsClosedImmersion.lift_fac (closι z) y.1 hk
    exact ⟨⟨IsClosedImmersion.lift (closι z) y.1 hk, by rw [← Category.assoc, hl, y.2]⟩, Subtype.ext hl⟩

end Local

theorem exists_compatChart {F : Type} [Field F] {X : Scheme.{0}} {p : X ⟶ Sp F} {σ : F →+* ℂ} {D : ℕ}
    [SmoothOfRelativeDimension D p] {A : FinHolAtlas D (CxPts p σ)} (hA : IsAlgAtlas A) (x : CxPts p σ)
    {N : Set (CxPts p σ)} (hN : N ∈ 𝓝 x) (V : X.affineOpens) (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V.1) {n : ℕ}
    (G : Fin n → Γ(X, V.1))
    (hR : FinalTheorems.Rsp (X.presheaf.stalk (x.1 (IsLocalRing.closedPoint ℂ))) n (fun j => X.presheaf.germ V.1 _ hV (G j))) :
    ∃ (hn : n ≤ D) (ψ : OpenPartialHomeomorph (CxPts p σ) (Fin D → ℂ)), IsCompatChart A ψ ∧ x ∈ ψ.source ∧
      ψ.source ⊆ N ∧ ψ.source ⊆ ptsIn p σ V.1 ∧
      ∀ y ∈ ψ.source, ∀ j, ψ y (Fin.castLE hn j) = ev p σ V.1 (G j) y := by
  haveI : CharZero F := σ.charZero
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := D) (p := p) (σ := σ) x
  have hli := SncChart.linearIndependent_fderiv_params F X p D σ c x hc V hV n G hR
  have hxV : x ∈ ptsIn p σ V.1 := mem_ptsIn.2 hV
  have h0 : ∀ i, ev p σ V.1 (G i) x = 0 := by
    intro i
    by_contra hne
    have hb := mem_ptsIn.1 ((mem_ptsIn_basicOpen hxV (G i)).2 hne)
    rw [Scheme.mem_basicOpen _ _ _ hV] at hb
    have hmem : X.presheaf.germ V.1 _ hV (G i) ∈ IsLocalRing.maximalIdeal _ := by
      rw [← hR.1]; exact Ideal.subset_span ⟨i, rfl⟩
    exact hmem hb
  have hn : n ≤ D := by
    have := hli.fintype_card_le_finrank
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ReciprocityTheory.L2DbarEstimates.V D) (F' := ℂ)).finrank_eq,
      Module.finrank_linearMap, Module.finrank_self, _root_.mul_one] at this
    simpa [ReciprocityTheory.L2DbarEstimates.V] using this
  obtain ⟨e, hx0, hsub, -, hhol, hsymm, hev⟩ :=
    SncChart.exists_chart_of_fderiv F X p D σ c x hc V.1 hxV n G h0 hli
  obtain ⟨O, hON, hO, hxO⟩ := mem_nhds_iff.1 hN
  let ψ := e.restrOpen O hO
  have hψs : ψ.source = e.source ∩ O := e.restrOpen_source O hO
  refine ⟨hn, ψ, ?_, hψs ▸ ⟨hx0, hxO⟩, fun y hy => hON (hψs ▸ hy).2, fun y hy => hsub (hψs ▸ hy).1,
    fun y hy j => hev y (hψs ▸ hy).1 (Fin.castLE hn j) j.2⟩
  refine GlobalTheory.DivSec.isCompatChart_of_holAlong F X p σ D A hA ψ (fun j => ?_) ?_
  · intro V _ _ _ B' y hB' hy hm
    exact hhol j V B' y hB' hy (fun b hb => (hψs ▸ hm hb).1)
  · exact GlobalTheory.LocLift.isHolTo_mono hsymm ψ.open_target fun z hz => hz.1

theorem isSNC_locSec : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ (A : FinHolAtlas D (CxPts p σ)), IsAlgAtlas A → ∀ (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (r : ℕ) (z : Fin r → X), Function.Injective z → (∀ a, Order.coheight (z a) = 1) → ((nonzeroLocus s : Set X)ᶜ = ⋃ a, closure {z a}) → (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → IsSNC A M.φ.locPot (M.φ.locSec (secVal p σ s)) (fun a => ((divOfSec M.φ.isLB s hs).mult (z a)).toNat) (fun a => Set.range (ptMap (closι (z a)) rfl σ)) := by
  intro F _ X _ _ p σ D _ hsm A hA M s hs r z hz hco hzero hsnc x
  classical
  haveI := hsm
  have hxi := mem_pick (p := p) (σ := σ) M.φ.isLB x
  have hi := mem_ptsIn.1 hxi
  obtain ⟨n, g, e, u, inst, hR, hI, hf⟩ :=
    GlobalTheory.SncForm.germ_eq_unit_mul_monomial X M.B M.φ.isLB s hs r z hz hco hzero _ (hsnc _) (pick M.φ.isLB x) hi
  obtain ⟨V, hV, G', hG'⟩ := GlobalTheory.DivSec.exists_affine_germ_eq X (x.1 (IsLocalRing.closedPoint ℂ)) (n + 1)
    (Fin.cons (u : X.presheaf.stalk _) g)
  let G : Fin n → Γ(X, V.1) := fun j => G' j.succ
  have hG : ∀ j, X.presheaf.germ V.1 _ hV (G j) = g j := fun j => hG' j.succ
  have hU : X.presheaf.germ V.1 _ hV (G' 0) = u := hG' 0
  have e1 := eventually_ev_eq x hi hV (s.f (pick M.φ.isLB x))
    (G' 0 * ∏ a, G (e a) ^ ((divOfSec M.φ.isLB s hs).mult (z a.1)).toNat) (by
      rw [hf, map_mul, map_prod, hU]
      simp only [map_pow, hG])
  have e2 := eventually_ev_ne_zero x hV (G' 0) (hU ▸ u.isUnit)
  have e3 := Filter.eventually_all.2 fun a => eventually_ev_eq_zero_iff x V hV (G (e a)) _ (by rw [hG]; exact hI a)
  have e4 : ∀ᶠ y in 𝓝 x, ∀ a, ¬ LiesIn x (Closeds.closure {z a}) → ¬ LiesIn y (Closeds.closure {z a}) :=
    Filter.eventually_all.2 fun a => by
      by_cases h : LiesIn x (Closeds.closure {z a})
      · exact Filter.Eventually.of_forall fun _ h' => absurd h h'
      · exact Filter.eventually_of_mem ((isOpen_not_liesIn _).mem_nhds h) fun y hy _ => hy
  have e5 : ∀ᶠ y in 𝓝 x, y ∈ M.φ.locPot.U x := (M.φ.locPot.isOpen_U x).mem_nhds (M.φ.locPot.mem_U x)
  obtain ⟨hn, ψ, hψ, hxψ, hN, hψV, hev⟩ := exists_compatChart hA x (e1.and (e2.and (e3.and (e4.and e5)))) V hV G
    (by rw [funext hG]; exact hR)
  let τ : Fin r → Option (Fin D) := fun a =>
    if h : x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a} then some (Fin.castLE hn (e ⟨a, h⟩)) else none
  refine ⟨ψ, hψ, hxψ, fun y hy => (hN hy).2.2.2.2, τ, ?_, ?_, ev p σ V.1 (G' 0), ?_, fun y hy => (hN hy).2.1, ?_⟩
  · intro a a' i h1 h2
    simp only [τ] at h1 h2
    split_ifs at h1 h2 with ha ha'
    have := Fin.castLE_injective hn ((Option.some.inj h1).trans (Option.some.inj h2).symm)
    exact congrArg Subtype.val (e.injective this)
  · intro a
    ext y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_range_ptMap_closι]
    refine and_comm.trans (and_congr_right fun hy => ?_)
    by_cases h : x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a}
    · simp only [τ, dif_pos h, Option.some.injEq, exists_eq_left', hev y hy]
      exact ((hN hy).2.2.1 ⟨a, h⟩).symm
    · simp only [τ, dif_neg h, reduceCtorEq, false_and, exists_false, iff_false]
      exact (hN hy).2.2.2.1 a h
  · exact (hA.holoOn_iff hA.anRead ψ.open_source).2 ((hA.anRead.holoOn_ev V.1 (G' 0)).mono hψV)
  · intro y hy
    refine (hN hy).1.trans ?_
    rw [ev_mul, ev_eq (hψV hy) (∏ _, _), map_prod,
      ← Fintype.prod_subtype_mul_prod_subtype (fun a => x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a})]
    congr 1
    rw [Finset.prod_eq_one (s := Finset.univ)
      (f := fun a : {a // ¬ x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a}} => _)
      (fun a _ => by simp only [τ, dif_neg a.2]), mul_one]
    refine Finset.prod_congr (by ext; simp) fun a _ => ?_
    simp only [τ, dif_pos a.2, map_pow, hev y hy, ev_eq (hψV hy)]

end GlobalTheory.SecSnc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteOfSurjectiveOfDimEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isFinite_of_surjective_of_dim_eq : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → Surjective f.hom.left → IsFinite f.hom.left := by
  intro K _ A B f hd hs
  have dB : SmoothOfRelativeDimension A.dim B.X.hom := hd ▸ B.smooth
  exact GlobalTheory.OntoFinite.isFinite_of_surjective A.ab B.ab A.smooth dB f.hom

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionLabelingGaloisConjugateAlgClosureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTorsionLabeling_galoisConjugate_algClosure : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) (k : ℕ), 1 ≤ k → ∀ (x x' : QkPt D.toPre (Kb R) k → (TFK (R := R) (Kb R) ⟶ A.A)), LabTors D.toPre A k x → (∀ p p', QkExt σ.toRingHom p p' → (x' p').left = spMap σ.toRingHom ≫ (x p).left) → LabTors D.toPre A k x' := by
  first | exact @GlobalTheory.Mum.labTors_galConj | exact GlobalTheory.Mum.labTors_galConj | (intros; apply GlobalTheory.Mum.labTors_galConj <;> assumption)
end

