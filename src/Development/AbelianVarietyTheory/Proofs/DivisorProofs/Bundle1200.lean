module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarGLRealPointsDensityDetInv
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

namespace GlobalTheory.GLHaar

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem lmul_apply (y x : Lie E a) : lmul y x = toL (Matrix.of y * Matrix.of x) := rfl

theorem lmul_lmul (y x : Lie E a) : lmul (lmul y x) = (lmul y).comp (lmul x) := by
  ext z : 1
  simp only [ContinuousLinearMap.comp_apply, lmul_apply]
  simp [Matrix.mul_assoc]

theorem lmul_one : lmul (toL (1 : Matrix (Fin a) (Fin a) (Cinf E))) = ContinuousLinearMap.id ℝ _ := by
  ext z : 1
  simp [lmul_apply]

def dL (x : Lie E a) : ℝ := LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)

theorem dL_mul (y x : Lie E a) : dL (lmul y x) = dL y * dL x := by
  unfold dL
  rw [lmul_lmul]
  exact LinearMap.det_comp (lmul y : Lie E a →ₗ[ℝ] Lie E a) (lmul x : Lie E a →ₗ[ℝ] Lie E a)

theorem lmul_add (x y : Lie E a) : lmul (x + y) = lmul x + lmul y := by
  ext z : 1
  exact Matrix.add_mul (Matrix.of x) (Matrix.of y) (Matrix.of z)

theorem lmul_smul (c : ℝ) (x : Lie E a) : lmul (c • x) = c • lmul x := by
  ext z : 1
  exact Matrix.smul_mul c (Matrix.of x) (Matrix.of z)

def lmulL : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) where
  toFun := lmul
  map_add' := lmul_add
  map_smul' := lmul_smul

theorem continuous_dL : Continuous (dL (E := E) (a := a)) :=
  ContinuousLinearMap.continuous_det.comp (LinearMap.continuous_of_finiteDimensional (lmulL (E := E) (a := a)))

open scoped ENNReal NNReal

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def jG (y : glG E a) : Lie E a := toL y.1.val

theorem jG_mul (g y : glG E a) : jG (g * y) = lmul (jG g) (jG y) := rfl

theorem jG_one : jG (1 : glG E a) = toL 1 := rfl

theorem isOpenEmbedding_jG : Topology.IsOpenEmbedding (jG (E := E) (a := a)) := by
  have hO : IsOpen ((glG E a : Subgroup (Matrix (Fin a) (Fin a) (Cinf E))ˣ) : Set (Matrix (Fin a) (Fin a) (Cinf E))ˣ) := by
    change IsOpen (Set.univ : Set (Matrix (Fin a) (Fin a) (Cinf E))ˣ)
    exact isOpen_univ
  exact GlobalTheory.CuspQuot.isOpenEmbedding_val.comp hO.isOpenEmbedding_subtypeVal

theorem range_jG : Set.range (jG (E := E) (a := a)) = invSet E a := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact val_mem_invSet y.1
  · intro hx
    exact ⟨⟨hx.unit, Subgroup.mem_top _⟩, hx.unit_spec⟩

theorem lmul_jG_inv (g : glG E a) (x : Lie E a) : lmul (jG g) (lmul (jG g⁻¹) x) = x := by
  rw [← ContinuousLinearMap.comp_apply, ← lmul_lmul, ← jG_mul, mul_inv_cancel, jG_one, lmul_one]
  rfl

theorem lmul_inv_jG (g : glG E a) (x : Lie E a) : lmul (jG g⁻¹) (lmul (jG g) x) = x := by
  rw [← ContinuousLinearMap.comp_apply, ← lmul_lmul, ← jG_mul, inv_mul_cancel, jG_one, lmul_one]
  rfl

theorem dL_one : dL (toL (1 : Matrix (Fin a) (Fin a) (Cinf E))) = 1 := by
  unfold dL
  rw [lmul_one]
  exact LinearMap.det_id

theorem dL_jG_ne (g : glG E a) : dL (jG g) ≠ 0 := by
  intro h
  have e := dL_mul (jG g) (jG g⁻¹)
  rw [← jG_mul, mul_inv_cancel, jG_one, dL_one, h, zero_mul] at e
  exact one_ne_zero e

theorem dL_ne_of_mem {x : Lie E a} (hx : x ∈ invSet E a) : dL x ≠ 0 := by
  rw [← range_jG] at hx
  obtain ⟨g, rfl⟩ := hx
  exact dL_jG_ne g

def rho (x : Lie E a) : ℝ≥0∞ := ENNReal.ofReal (|dL x|⁻¹)

theorem measurable_rho : Measurable (rho (E := E) (a := a)) :=
  ENNReal.measurable_ofReal.comp (continuous_dL.abs.measurable.inv)

theorem ofReal_mul_rho (y x : Lie E a) (hy : dL y ≠ 0) :
    ENNReal.ofReal |dL y| * rho (lmul y x) = rho x := by
  unfold rho
  rw [← ENNReal.ofReal_mul (abs_nonneg _), dL_mul, abs_mul, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (abs_ne_zero.2 hy), one_mul]

def muG [MeasurableSpace (glG E a)] (ν : MeasureTheory.Measure (Lie E a)) : MeasureTheory.Measure (glG E a) :=
  (ν.withDensity rho).comap jG

section Haar

variable [MeasurableSpace (glG E a)] [BorelSpace (glG E a)] (ν : Measure (Lie E a)) [hν : ν.IsAddHaarMeasure]

theorem mE : MeasurableEmbedding (jG (E := E) (a := a)) := isOpenEmbedding_jG.measurableEmbedding

theorem withDensity_preimage (g : glG E a) {A : Set (Lie E a)} (hA : MeasurableSet A) :
    ν.withDensity rho (lmul (jG g) ⁻¹' A) = ν.withDensity rho A := by
  set L := lmul (jG g)
  have hsurj : L '' (L ⁻¹' A) = A := Set.image_preimage_eq A (fun x => ⟨lmul (jG g⁻¹) x, lmul_jG_inv g x⟩)
  have hinj : Function.Injective L := fun x y h => by
    rw [← lmul_inv_jG g x, ← lmul_inv_jG g y]
    exact congrArg _ h
  have hS : MeasurableSet (L ⁻¹' A) := hA.preimage L.continuous.measurable
  rw [withDensity_apply _ hA, withDensity_apply _ hS]
  conv_rhs => rw [← hsurj]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul ν hS (fun x _ => L.hasFDerivAt.hasFDerivWithinAt)
    hinj.injOn]
  refine setLIntegral_congr_fun hS (fun x _ => ?_)
  exact (ofReal_mul_rho (jG g) x (dL_jG_ne g)).symm

theorem muG_leftInv : (muG ν : Measure (glG E a)).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext s hs
  have hm : Measurable (g * · : glG E a → glG E a) := (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hm hs, muG, mE.comap_apply, mE.comap_apply]
  have himg : jG '' ((g * ·) ⁻¹' s) = (lmul (jG g)) ⁻¹' (jG '' s) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g * y, hy, rfl⟩
    · rintro ⟨z, hz, hzx⟩
      refine ⟨g⁻¹ * z, ?_, ?_⟩
      · show g * (g⁻¹ * z) ∈ s
        rwa [mul_inv_cancel_left]
      · show lmul (jG g⁻¹) (jG z) = x
        rw [hzx, lmul_inv_jG]
  rw [himg]
  exact withDensity_preimage ν g (mE.measurableSet_image.2 hs)

theorem muG_finite : IsFiniteMeasureOnCompacts (muG ν : Measure (glG E a)) := by
  refine ⟨fun K hK => ?_⟩
  rw [muG, mE.comap_apply]
  have hK' : IsCompact (jG '' K) := hK.image isOpenEmbedding_jG.continuous
  have hsub : jG '' K ⊆ invSet E a := by
    rw [← range_jG]
    exact Set.image_subset_range _ _
  rw [withDensity_apply _ hK'.measurableSet]
  have hc : ContinuousOn (fun x : Lie E a => |dL x|⁻¹) (jG '' K) :=
    continuous_dL.abs.continuousOn.inv₀ fun x hx => abs_ne_zero.2 (dL_ne_of_mem (hsub hx))
  exact (hc.integrableOn_compact hK').lintegral_lt_top

theorem muG_pos : (muG ν : Measure (glG E a)).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [muG, mE.comap_apply]
  intro h0
  rw [withDensity_apply_eq_zero' measurable_rho.aemeasurable] at h0
  have he : {x | rho x ≠ 0} ∩ jG '' U = jG '' U := by
    refine Set.inter_eq_right.2 ?_
    rintro _ ⟨y, _, rfl⟩
    exact (ENNReal.ofReal_pos.2 (inv_pos.2 (abs_pos.2 (dL_jG_ne y)))).ne'
  rw [he] at h0
  exact (isOpenEmbedding_jG.isOpenMap U hU).measure_ne_zero ν (hne.image _) h0

theorem muG_haar : (muG ν : Measure (glG E a)).IsHaarMeasure :=
  haveI := muG_leftInv ν
  haveI := muG_finite ν
  haveI := muG_pos ν
  { }

theorem integral_muG (Φ : Lie E a → ℂ) (hΦ : ∀ x ∉ invSet E a, Φ x = 0) :
    ∫ y, Φ (toL y.1.val) ∂(muG ν : Measure (glG E a)) =
      ∫ x, ((|LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)|⁻¹ : ℝ) : ℂ) * Φ x ∂ν := by
  change ∫ y, Φ (jG y) ∂(muG ν) = _
  rw [← mE.integral_map, muG, mE.map_comap, range_jG, setIntegral_eq_integral_of_forall_compl_eq_zero hΦ]
  have hf : Measurable fun x : Lie E a => (|dL x|⁻¹).toNNReal := continuous_dL.abs.measurable.inv.real_toNNReal
  change ∫ x, Φ x ∂(ν.withDensity fun x => (((|dL x|⁻¹).toNNReal : ℝ≥0) : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.2 (abs_nonneg _)), Complex.real_smul]
  rfl

end Haar

theorem glHaar : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ (ν : Measure (Lie E a)), ν.IsAddHaarMeasure → ∀ [MeasurableSpace (glG E a)] [BorelSpace (glG E a)], ∃ μ : Measure (glG E a), μ.IsHaarMeasure ∧ ∀ (Φ : Lie E a → ℂ), ContinuousOn Φ (invSet E a) → (∀ x ∉ invSet E a, Φ x = 0) → ∫ y, Φ (toL y.1.val) ∂μ = ∫ x, ((|LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)|⁻¹ : ℝ) : ℂ) * Φ x ∂ν := by
  intro E _ _ _ a ν hν _ _
  exact ⟨muG ν, muG_haar ν, fun Φ _ hΦ => integral_muG ν Φ hΦ⟩

end GlobalTheory.GLHaar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactLevelSphericalOffTypes
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrMult.OneLevel

variable {D : D7}

def levelAd {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : Subgroup (GA D V) :=
  levelOpen D.sp.cm.sig V.gram (frameLat V) ⊓
    (⨅ v : T.S, (stabLocOne D.sp.cm.sig V.gram (T.frame v).emb (frameLat V)).comap (proj D.sp.cm.sig V.gram v.1)) ⊓
    U.frame.iwahori.comap (proj D.sp.cm.sig V.gram U.u)

def level {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : Subgroup (GfC V) := (levelAd T U).subgroupOf (GfC V)

theorem mem_levelAd {V : HSp D} {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} {g : GA D V} :
    g ∈ levelAd T U ↔ (∀ v, proj D.sp.cm.sig V.gram v g ∈ Kv V v) ∧
      (∀ v : T.S, proj D.sp.cm.sig V.gram v.1 g ∈ stabLocOne D.sp.cm.sig V.gram (T.frame v).emb (frameLat V)) ∧
      proj D.sp.cm.sig V.gram U.u g ∈ U.frame.iwahori := by
  simp [levelAd, mem_levelOpen, Subgroup.mem_iInf, and_assoc]

theorem isOpen_levelAd {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : IsOpen (levelAd T U : Set (GA D V)) := by
  let : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  simp only [levelAd, Subgroup.coe_inf, Subgroup.coe_iInf, Subgroup.coe_comap]
  refine ((isOpen_levelOpen _ _ _).inter (isOpen_iInter_of_finite fun v => ?_)).inter
    (U.frame.isOpen_iwahori.preimage (continuous_proj _ _ _))
  exact (isOpen_stabLocOne _ _ _ (isCMExt_host D)).preimage (continuous_proj _ _ _)

theorem isClosed_levelAd {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : IsClosed (levelAd T U : Set (GA D V)) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_levelAd T U)

theorem isOpen_level {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : IsOpen (level T U : Set (GfC V)) := by
  rw [level, Subgroup.coe_subgroupOf]
  exact (isOpen_levelAd T U).preimage continuous_subtype_val

theorem isCompact_level {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : IsCompact (level T U : Set (GfC V)) := by
  let : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  rw [Subtype.isCompact_iff]
  have e : ((↑) : GfC V → GA D V) '' (level T U : Set (GfC V)) =
      (levelFin D.sp.cm.sig V.gram (frameLat V) : Set (GA D V)) ∩ levelAd T U := by
    ext g
    simp only [level, Set.mem_image, SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_inter_iff, mem_levelFin]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.2, (mem_levelAd.1 hx).1⟩, hx⟩
    · rintro ⟨⟨hf, -⟩, hg⟩
      exact ⟨⟨g, hf⟩, hg, rfl⟩
  rw [e]
  exact (isCompact_levelFin _ _ _).inter_right (isClosed_levelAd T U)

theorem conv_mul_left {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    {f f' : G → ℂ} {a : G} (ha : ∀ y, f (a * y) = f y) (x : G) : conv μ f f' (a * x) = conv μ f f' x := by
  simp only [conv]
  rw [← integral_mul_left_eq_self _ a]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [ha, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

end GlobalTheory.TrMult.OneLevel


open GlobalTheory.TrMult.OneLevel in
theorem GlobalTheory.TrMult.oneLevel : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), ∃ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) ∧ IsCompact (K : Set (GfC V)) ∧ ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → ∀ ff, IsTestFin T U μf ff → SphRest T U ff → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff ∧ ∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g := by
  intro D V T U
  let : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  refine ⟨level T U, isOpen_level T U, isCompact_level T U, fun μf hμ ff hT hS => ⟨hT.isFinFamily, fun k hk g => ?_⟩⟩
  obtain ⟨hK, hOne, hI⟩ := mem_levelAd.1 (Subgroup.mem_subgroupOf.1 hk)
  simp only [finFn]
  refine finprod_congr fun v => ?_
  rw [Subgroup.coe_mul, map_mul]
  generalize proj D.sp.cm.sig V.gram v (g : GA D V) = x
  by_cases hv : v ∈ T.S
  · obtain ⟨h, -, e⟩ := hT.2.1 ⟨v, hv⟩
    have he : ∀ y, T.idem μf ⟨v, hv⟩ (proj D.sp.cm.sig V.gram v (k : GA D V) * y) = T.idem μf ⟨v, hv⟩ y := fun y =>
      (typeIdem_mul_ker (μf v) (T.frame ⟨v, hv⟩).red (T.τ ⟨v, hv⟩) (k := ⟨_, hK v⟩)
        (((T.frame ⟨v, hv⟩).red_eq_one_iff _).2 (hOne ⟨v, hv⟩)) y).1
    simp only at e
    rw [e]
    exact conv_mul_left _ (conv_mul_left _ he) x
  · by_cases hu : v = U.u
    · subst hu
      obtain ⟨t, -, e⟩ := hT.2.2.1
      rw [e]
      simp only [SplitAt.cosetFn, SplitAt.iwahoriCoset, Set.indicator]
      congr 1
      apply propext
      rw [DoubleCoset.mem_doubleCoset, DoubleCoset.mem_doubleCoset]
      constructor
      · rintro ⟨a, ha, b, hb, e⟩
        refine ⟨(proj D.sp.cm.sig V.gram U.u (k : GA D V))⁻¹ * a, mul_mem (inv_mem hI) ha, b, hb, ?_⟩
        simp only [mul_assoc]
        rw [eq_inv_mul_iff_mul_eq]
        simpa only [mul_assoc] using e
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨_ * a, mul_mem hI ha, b, hb, by group⟩
    · simpa using hS v hv hu _ (hK v) 1 (one_mem _) x
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveVarietyOfIsLocalRingOfVarietyPoi
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocModelProj


open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw in
theorem exists_projective_openImmersion (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (p : Y ⟶ Sp ℂ) (j : Sp S ⟶ Y),
      IsProjOver p ∧ IsOpenImmersion j ∧ LocallyOfFiniteType p ∧ j ≫ p = spMap (algebraMap ℂ S) := by
  have : LocallyOfFiniteType (spMap (algebraMap ℂ S)) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  obtain ⟨N, i, _, _, e⟩ := (isAmpleLB_of_isAffine (LB.isLB_triv (Sp S))).isQProjOver (spMap (algebraMap ℂ S))
  have := isProper_str ℂ N
  exact ⟨i.image, isIntegral_image i, i.imageι ≫ PSpace.str ℂ N, i.toImage, ⟨N, i.imageι, inferInstance, rfl⟩,
    inferInstance, inferInstance, by rw [i.toImage_imageι_assoc, e]⟩

theorem topologicalKrullDim_eq_of_openImmersion (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (Y : Scheme.{0}) [IsIntegral Y]
    (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] (j : Sp S ⟶ Y) [IsOpenImmersion j] (n : ℕ) (h : Algebra.trdeg ℂ S = n) :
    topologicalKrullDim Y = n := by
  have : Nonempty (Sp S) := inferInstance
  rw [← GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion ℂ Y (Sp S) p j]
  change topologicalKrullDim (PrimeSpectrum S) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, GlobalTheory.ringKrullDim_eq_of_trdeg_eq ℂ S h]

theorem exists_projective_of_isLocModel : ∀ (L : Type) [Field L] (c : ℂ →+* L) (R : Subring L) (n : ℕ) (x : Fin n → L), IsLocModel c R → TrBasis c x →
  ∃ (Y : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral Y) (p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) (e : Y.functionField ≃+* L) (y : Y),
    IsProjOver p ∧ topologicalKrullDim Y = n ∧ (∀ a, e (GlobalTheory.Cartier.constFn p a) = c a) ∧ (locRing y).map e.toRingHom = R := by
  intro L _ c R n x hR hx
  obtain ⟨S, hS, q, hq, hft, hfrac, hmem⟩ := _root_.GlobalTheory.FieldPair.IsLocModel.exists_finiteType_localization L c R hR
  letI : Algebra ℂ S := (c.codRestrict S hS).toAlgebra
  letI : Algebra S L := S.subtype.toAlgebra
  letI : Algebra ℂ L := c.toAlgebra
  haveI : IsScalarTower ℂ S L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType ℂ S := hft
  haveI : FaithfulSMul S L := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI : IsFractionRing S L := by
    refine IsFractionRing.of_field S L fun f => ?_
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hfrac f
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change f = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  have htr : Algebra.trdeg ℂ S = n := by
    have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
    have : Algebra.IsAlgebraic S L := IsLocalization.isAlgebraic L (nonZeroDivisors S)
    rw [← trdeg_add_eq ℂ S (A := L), trdeg_eq_zero (R := S) (A := L), add_zero] at h2
    rw [← h2, Cardinal.mk_fin]
  obtain ⟨Y, hY, p, j, hproj, hj, hlft, hjp⟩ := exists_projective_openImmersion S
  obtain ⟨e, hc, hloc⟩ := GlobalTheory.T.exists_functionFieldEquiv_openImmersionSpec S Y p j hjp
  let e2 : FractionRing S ≃ₐ[S] L := IsLocalization.algEquiv (nonZeroDivisors S) (FractionRing S) L
  refine ⟨Y, hY, p, e.trans e2.toRingEquiv, j.base ⟨q, hq⟩, hproj, topologicalKrullDim_eq_of_openImmersion S Y p j n htr, fun a => ?_, ?_⟩
  · change e2 (e (GlobalTheory.Cartier.constFn p a)) = c a
    rw [hc, IsScalarTower.algebraMap_apply ℂ S (FractionRing S), AlgEquiv.commutes]
    rfl
  · ext g
    have h1 : g ∈ (locRing (j.base ⟨q, hq⟩)).map (e.trans e2.toRingEquiv).toRingHom ↔
        e2.symm g ∈ (locRing (j.base ⟨q, hq⟩)).map e.toRingHom := by
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, by simp⟩
      · rintro ⟨u, hu, hu'⟩
        refine ⟨u, hu, ?_⟩
        change e2 (e u) = g
        rw [show e u = e2.symm g from hu', AlgEquiv.apply_symm_apply]
    rw [h1, hloc ⟨q, hq⟩, hmem g]
    refine exists₂_congr fun a b => and_congr_right fun _ => ?_
    constructor
    · intro h
      have := congrArg e2 h
      rwa [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes] at this
    · intro h
      apply e2.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes]
      exact h

end GlobalTheory.LocModelProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictedProductHaarGivenFiniteFactors
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ProdMeas

theorem exists_isFinMeas {D : D7} (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) [∀ v, (μf v).IsHaarMeasure]
    (h1 : ∀ᶠ v in cofinite, μf v (Kv V v) = 1) : ∃ ν, IsFinMeas V μf ν := by
  obtain ⟨ν, hν⟩ := (existsUnique_isRestrictedProdFinPts D.sp.cm.sig V.gram (frameLat V) μf h1).exists
  refine ⟨ν, hν.2.2.1, fun ff hf => ?_⟩
  let S := (eventually_cofinite.1 (hf.2.and h1)).toFinset
  have hS : ∀ v ∉ S, ff v = unitLoc _ _ (frameLat V) v ∧ μf v (Kv V v) = 1 := fun v hv => by
    simpa only [S, Finite.mem_toFinset, mem_setOf_eq, not_not] using hv
  rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ fun v hv => by_contra fun h => hv (by
    rw [(hS v h).1, unitLoc]
    refine (integral_indicator_const _ (isOpen_stabLoc _ _ _ v).measurableSet).trans ?_
    rw [Measure.real, (hS v h).2, ENNReal.toReal_one, one_smul]; rfl)]
  have hcount : Countable (HeightOneSpectrum (𝓞 D.host.F)) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum _
  have hsf : ∀ w : Empty, SigmaFinite (w.elim : Measure PUnit.{1}) := fun w => w.elim
  have key := (GlobalTheory.RestrMeas.IsCylProd.integral_tensor_indicator (𝕜 := ℂ) (fa := fun w => w.elim) (ff := ff) hν.2.2.2
    (fun w => w.elim) (fun v => ((continuous_proj _ _ v).comp continuous_subtype_val).measurable)
    (fun v => (isOpen_stabLoc _ _ _ v).measurableSet) (fun x => eventually_proj_mem_stabLoc _ _ _ x.1)
    (S := S) (fun v hv => (hS v hv).2) (fun v hv => (hS v hv).1) (fun w => w.elim)
    fun v _ => (hf.1 v).1.continuous.integrable_of_hasCompactSupport (hf.1 v).2).2
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul] at key
  exact key

end GlobalTheory.ProdMeas

namespace GlobalTheory.ProdMeas

theorem exists_prod_of_haar : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) →
    (∃ μa, IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ) ∧ ∃ ν, IsFinMeas V μf ν := by
  intro D V μ _ μf hf h1
  haveI := hf
  refine ⟨?_, exists_isFinMeas V μf h1⟩
  obtain ⟨μ₀, h₀⟩ := (existsUnique_isRestrictedProd D.sp.cm.sig V.gram (frameLat V) (fun _ => Measure.haar) μf h1).exists
  haveI := h₀.haar
  have he : μ = Measure.haarScalarFactor μ μ₀ • μ₀ := Measure.isMulLeftInvariant_eq_smul μ μ₀
  have hc : Measure.haarScalarFactor μ μ₀ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at he
    exact (NeZero.ne μ) he
  classical
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace D.host.F))
  rw [he]
  exact ⟨_, h₀.smul_arch w hc⟩

end GlobalTheory.ProdMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMonomialAtOriginGaussianEntireOrthonormal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockPos

theorem fock_monomial_zero_of_on : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), IsStdChar D ψ (-1) → IsInfFam θ → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ (F : WO S T → ℂ) (Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ), Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → F w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) F (MvPolynomial.monomial k 1) 0 = (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ (k.sum fun _ n => n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Φ := by
  intro D ψ θ S T frS frT hψ hθ hS hT F Φ hΦ hF k
  have hS' : ∀ τ, (frAt frS τ)ᴴ * gramAt D S τ * frAt frS τ = 1 := frAt_on frS hS
  have hT' : ∀ τ, (frAt frT τ)ᴴ * gramAt D T τ * frAt frT τ = 1 := frAt_on frT hT
  exact GlobalTheory.FockJetOrigin.fock_monomial_zero θ hS' hT' hψ hθ F Φ hΦ (fun w hw => hF w hw) k

end GlobalTheory.FockPos
end

