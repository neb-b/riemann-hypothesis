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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureMapPullbackGenericallyFinite
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.Mix.map_part_pull_of_genFinite : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (L : Fin D → MLine p σ) (ε : ℤˣ), Measure.map (ptMap π hπ σ) (part (fun i => (L i).pull π hπ) ε) = (π.residueDegree (genericPoint Y) : ENNReal) • part L ε := by
  intro F _ X Y _ _ p q σ D hp hD hq π hπ hgen hdeg L ε
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hp
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hq
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hp
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hq
  haveI : IsLocallyNoetherian X := by
    obtain ⟨N, i, _, rfl⟩ := hp
    have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str F N
    exact LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str F N)
  obtain ⟨U, hU, hfibU, hchU⟩ := _root_.GlobalTheory.CoverDegProj.exists_open_covering_charts F X Y p q σ D hp hq π hπ hgen hdeg
  obtain ⟨U', hU', hcharts⟩ := _root_.GlobalTheory.GenericCharts.exists_generic_charts F X p σ D hp hD
  set m := ptMap π hπ σ with hm_def
  set Z : Set X := ((U ⊓ U' : X.Opens) : Set X)ᶜ with hZ_def
  have hZ : IsClosed Z := (U ⊓ U').isOpen.isClosed_compl
  have hgZ : genericPoint X ∉ Z := fun h => h ⟨hU, hU'⟩
  set T : Set (CxPts p σ) := (ptsIn p σ (U ⊓ U'))ᶜ with hT_def
  have hTset : T = {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} := by
    ext y
    simp only [hT_def, hZ_def, mem_compl_iff, mem_setOf_eq, mem_ptsIn]
    rfl
  have hmT : m ⁻¹' T = {z : CxPts q σ | z.1 (IsLocalRing.closedPoint ℂ) ∈ π ⁻¹' Z} := by
    rw [hTset]
    ext z
    simp only [mem_preimage, mem_setOf_eq, hm_def, ptMap, PtsOver.map_val]
    rfl
  have hZ' : IsClosed (π ⁻¹' Z : Set Y) := hZ.preimage π.continuous
  have hgZ' : genericPoint Y ∉ (π ⁻¹' Z : Set Y) := by
    simp only [mem_preimage, hgen]
    exact hgZ
  have hm : Continuous m := PtsOver.continuous_map π hπ (spMap σ)
  refine GlobalTheory.GlueCoverNull.map_glueMeas_of_cover D (CxPts p σ) (CxPts q σ) (AlgChart p σ D) (AlgChart q σ D)
    (fun c => c.e) (fun c y => ENNReal.ofReal ((ε : ℤ) * dens L c y))
    (fun c => c.e) (fun c y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y))
    (fun i j => i.holo_trans j) ?_ (fun i j => i.holo_trans j) ?_ m hm T
    (isOpen_ptsIn _).isClosed_compl ?_ ?_ _ ?_ ?_
  · intro i j y hi hj
    rw [_root_.GlobalTheory.Mix.ChartChange.dens_change_chart F X p σ D L i j y hi hj, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  · intro i j y hi hj
    rw [_root_.GlobalTheory.Mix.ChartChange.dens_change_chart F Y q σ D _ i j y hi hj, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  · intro c
    rw [hTset]
    exact GlobalTheory.ChernNull.chart_null_field F X p σ D Z hZ hgZ c
  · intro c
    rw [hmT]
    exact GlobalTheory.ChernNull.chart_null_field F Y q σ D _ hZ' hgZ' c
  · intro x hx
    have hx' : x ∈ ptsIn p σ (U ⊓ U') := not_not.1 hx
    exact hfibU x (mem_ptsIn_inf.1 hx').1
  · intro z hz
    have hz' := mem_ptsIn_inf.1 (not_not.1 hz : m z ∈ ptsIn p σ (U ⊓ U'))
    obtain ⟨c, hc⟩ := hcharts (m z) hz'.2
    obtain ⟨c', hzc', hw⟩ := hchU z hz'.1 c hc
    refine ⟨c, c', hzc', hc, fun w hwc' _ => ⟨(hw w hwc').2, ?_⟩⟩
    rw [_root_.GlobalTheory.MixPull.dens_pull F X Y p q σ D π hπ L c c' hw w hwc']
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasurePullbackEqZeroOfLtDim
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixDrop

theorem part_pull_eq_zero : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D D' : ℕ), D' < D → IsProjOver p → topologicalKrullDim X = (D' : ℕ) → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ (L : Fin D → MLine p σ) (ε : ℤˣ), part (fun i => (L i).pull π hπ) ε = 0 := by
  intro F _ X Y _ _ p q σ D D' hD hp hX hq π hπ hgen L ε
  have hLN : IsLocallyNoetherian X := by
    obtain ⟨N, ι, _, h⟩ := hp
    have : LocallyOfFiniteType p := h ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨U, hU, hch⟩ := GlobalTheory.GenericCharts.exists_generic_charts F X p σ D' hp hX
  have hgU : genericPoint Y ∈ π ⁻¹ᵁ U := by
    show π (genericPoint Y) ∈ U
    rw [hgen]; exact hU
  have hnull := GlobalTheory.MixNull.part_compl_null F Y q σ σ.injective hq D (fun i => (L i).pull π hπ) ε (π ⁻¹ᵁ U) hgU
  have hz : ∀ (c : AlgChart q σ D) (w : CxPts q σ), w ∈ c.e.source → w ∈ ptsIn q σ (π ⁻¹ᵁ U) →
      dens (fun i => (L i).pull π hπ) c w = 0 := by
    intro c w hw hwU
    have hm : ptMap π hπ σ w ∈ ptsIn p σ U := by
      rw [mem_ptsIn] at hwU ⊢
      exact hwU
    obtain ⟨c0, hc0⟩ := hch _ hm
    obtain ⟨ξ, hξ, hker⟩ := _root_.GlobalTheory.HessKer.exists_common_kernel F X Y p q σ D D' hD π hπ c0 c w hw hc0
    have hdet : ∀ τ : Equiv.Perm (Fin D), (Matrix.of fun j l =>
        c.hess ((L (τ l)).pull π hπ).φ (pick ((L (τ l)).pull π hπ).φ.isLB w) w j l).det = 0 := by
      intro τ
      refine (Matrix.exists_vecMul_eq_zero_iff).1 ⟨ξ, hξ, funext fun l => ?_⟩
      have h1 := congrFun (hker (L (τ l)) (pick ((L (τ l)).pull π hπ).φ.isLB w) (mem_pick _ w)) l
      simpa [Matrix.vecMul, dotProduct] using h1
    unfold dens
    simp only [hdet, Finset.sum_const_zero, Complex.zero_re, mul_zero]
  have hc : ∀ c : AlgChart q σ D, chartMeas c.e
      (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y)) = 0 := by
    intro c
    set S := ptsIn q σ (π ⁻¹ᵁ U) with hSdef
    have hS : MeasurableSet S := (isOpen_ptsIn _).measurableSet
    have h1 : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y)) S = 0 := by
      rw [chartMeas_apply c.e _ hS]
      refine (setLIntegral_congr_fun (measurableSet_image _ (c.e.open_source.measurableSet.inter hS)
        inter_subset_left) ?_).trans lintegral_zero
      rintro _ ⟨y, hy, rfl⟩
      show ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c (c.e.symm (c.e y))) = 0
      rw [c.e.left_inv hy.1, hz c y hy.1 hy.2, mul_zero, ENNReal.ofReal_zero]
    have hle : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y)) ≤
        part (fun i => (L i).pull π hπ) ε :=
      le_iSup (fun c : AlgChart q σ D => chartMeas c.e
        (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y))) c
    have h2 := (Measure.le_iff'.1 hle Sᶜ).trans_eq hnull
    refine Measure.measure_univ_eq_zero.1 (le_antisymm ?_ bot_le)
    calc _ ≤ _ := measure_mono (show univ ⊆ S ∪ Sᶜ by simp)
      _ ≤ _ := measure_union_le _ _
      _ ≤ 0 := by rw [h1, zero_add]; exact h2
  show glueMeas _ _ = 0
  unfold glueMeas
  simp only [hc]
  exact le_antisymm (iSup_le fun _ => le_rfl) (Measure.zero_le _)

end GlobalTheory.MixDrop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulipointLiftToFinerLevelCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

namespace GlobalTheory.LevelLift

open scoped TensorProduct

theorem exists_field_over (K F M : Type) [Field K] [Field F] [Field M] [Algebra K F] [FiniteDimensional K F]
    (io : K →+* M) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : Algebra M L₀) (_ : FiniteDimensional M L₀) (io' : F →+* L₀),
      io'.comp (algebraMap K F) = (algebraMap M L₀).comp io := by
  letI : Algebra K M := io.toAlgebra
  haveI : Nontrivial (M ⊗[K] F) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K M F io.injective
      (algebraMap K F).injective
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (M ⊗[K] F)
  letI : Field (M ⊗[K] F ⧸ I) := Ideal.Quotient.field I
  refine ⟨M ⊗[K] F ⧸ I, inferInstance, inferInstance, inferInstance,
    (Ideal.Quotient.mk I).comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  ext k
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply K M (M ⊗[K] F), Ideal.Quotient.mk_algebraMap]
  rfl

theorem exists_point_finite_surjective {X Y : Scheme.{0}} (f : X ⟶ Y) (hf : IsFinite f) (hs : Surjective f)
    (L₀ : Type) [Field L₀] (y : Sp L₀ ⟶ Y) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra L₀ L) (_ : FiniteDimensional L₀ L) (x : Sp L ⟶ X),
      x ≫ f = spMap (algebraMap L₀ L) ≫ y := by
  haveI := hf
  haveI := hs
  haveI : Surjective (pullback.snd f y) := inferInstance
  haveI : IsAffine (pullback f y) := isAffine_of_isAffineHom (pullback.snd f y)
  let P := pullback f y
  let g' : Spec Γ(P, ⊤) ⟶ Sp L₀ := P.isoSpec.inv ≫ pullback.snd f y
  haveI : IsFinite g' := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g'
  have hφf : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  haveI : Nonempty (Sp L₀) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨p, -⟩ := (pullback.snd f y).surjective (Classical.arbitrary (Sp L₀))
  haveI : Nontrivial Γ(P, ⊤) := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨P.isoSpec.hom p⟩
  obtain ⟨I, hI⟩ := Ideal.exists_maximal Γ(P, ⊤)
  letI : Field (Γ(P, ⊤) ⧸ I) := Ideal.Quotient.field I
  letI : Algebra L₀ (Γ(P, ⊤) ⧸ I) := ((Ideal.Quotient.mk I).comp φ.hom).toAlgebra
  have hfin : ((Ideal.Quotient.mk I).comp φ.hom).Finite :=
    RingHom.Finite.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) hφf
  refine ⟨Γ(P, ⊤) ⧸ I, inferInstance, inferInstance, hfin,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ P.isoSpec.inv ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc P.isoSpec.inv]
  change _ ≫ g' ≫ y = _
  rw [← hφ, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem lift_to_finer_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l₂ : Level H) (Xo : Moduli Dw l) (Xo₂ : Moduli Dw l₂) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.Dvd l₂ → l₂.A = l.A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∃ (c₂ : Coeff l₂) (la₂ : HeightOneSpectrum (𝓞 c₂.F)) (T' : CDVR) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V) (e' : ℕ) (io₂ : c₂.F →+* T'.Fr) (e₂ : ℕ) (x₂ : Sp T'.Fr ⟶ Xo₂.X) (r : Xo₂.X ⟶ Xo.X) (_ : SABMap Xo₂.univ.t Xo.univ.t r), 0 < e' ∧ (∀ a : T.Fr, vV T'.V (iT a) = (e' : ℤ) * vV T.V a) ∧ (∀ a : T.V, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) ∧ OverLa la₂ T'.V io₂ e₂ ∧ x₂ ≫ Xo₂.s = spMap (io₂.comp (IntermediateField.inclusion c₂.le).toRingHom) ∧ x₂ ≫ r = spMap iT ≫ x := by
  intro E _ _ _ H Dw l l₂ Xo Xo₂ c hpq hd hA la T io e ho x hx
  obtain ⟨r, jK, m, -, -, -, -, -, hrF⟩ :=
    ((GlobalTheory.moduliScheme_levelMaps_heckePoints).2 E H Dw hpq).1 l l₂ Xo Xo₂ hd
  let F₂ : IntermediateField ℚ ℂ := c.F ⊔ IntermediateField.adjoin ℚ {zeta l₂.M'}
  have hle : c.F ≤ F₂ := le_sup_left
  have hpos : 0 < l₂.M' := Nat.lcm_pos (by have := l₂.three_le; omega) l₂.A_pos
  have hint : IsIntegral ℚ (zeta l₂.M') :=
    ((Complex.isPrimitiveRoot_exp l₂.M' hpos.ne').isIntegral hpos).tower_top
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta l₂.M'}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hfin : FiniteDimensional ℚ F₂ := IntermediateField.finiteDimensional_sup _ _
  have hKA : KA l₂ = KA l := by unfold KA; rw [hA]
  let c₂ : Coeff l₂ :=
    { F := F₂, fin := hfin, conj := fun τ a => hle (c.conj τ a),
      zeta_mem := le_sup_right (a := c.F) (IntermediateField.subset_adjoin ℚ _ rfl),
      le := hKA ▸ c.le.trans hle }
  let c' : Coeff l :=
    { F := F₂, fin := hfin, conj := fun τ a => hle (c.conj τ a), zeta_mem := hle c.zeta_mem,
      le := c.le.trans hle }
  obtain ⟨rF, hr1, hr2, hfinr, -, hsurj, -⟩ := hrF c' c₂ rfl
  letI : Algebra c.F F₂ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ c.F F₂ := IsScalarTower.of_algebraMap_eq fun q => by
    simp
  haveI : FiniteDimensional c.F F₂ := Module.Finite.of_restrictScalars_finite ℚ c.F F₂
  obtain ⟨L₀, _, _, _, io', hio'⟩ := exists_field_over c.F F₂ T.Fr io
  have cond : (spMap (algebraMap T.Fr L₀) ≫ x) ≫ Xo.s =
      spMap io' ≫ spMap (IntermediateField.inclusion c'.le).toRingHom := by
    rw [Category.assoc, hx, Formalism.L2.PjFree.spMap_comp', Formalism.L2.PjFree.spMap_comp']
    congr 1
    ext a
    have h := RingHom.congr_fun hio' (IntermediateField.inclusion c.le a)
    exact h.symm
  let z' : Sp L₀ ⟶ Xo.XF c' := pullback.lift (spMap (algebraMap T.Fr L₀) ≫ x) (spMap io') cond
  obtain ⟨L, _, _, _, x', hx'⟩ := exists_point_finite_surjective rF hfinr hsurj L₀ z'
  letI : Algebra T.Fr L := ((algebraMap L₀ L).comp (algebraMap T.Fr L₀)).toAlgebra
  haveI : IsScalarTower T.Fr L₀ L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional T.Fr L := Module.Finite.trans L₀ L
  obtain ⟨T', iT, e', ψ, φ, he', hv, hψ, hφ, -⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L
  let io₂ : c₂.F →+* T'.Fr := ψ.toRingHom.comp ((algebraMap L₀ L).comp io')
  haveI : NumberField c₂.F := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  obtain ⟨la₂, e₂, ho₂⟩ := GlobalTheory.LocalDepthCompare.exists_overLa_of_not_charZero (V := T'.V) io₂
    (GlobalTheory.LocalDepthCompare.not_charZero_of_overLa (ho.bc iT he' hv))
  have hid : spMap (IntermediateField.inclusion (le_of_eq (rfl : c'.F = c₂.F))).toRingHom = 𝟙 (Sp c₂.F) := by
    have : (IntermediateField.inclusion (le_of_eq (rfl : c'.F = c₂.F))).toRingHom = RingHom.id _ :=
      RingHom.ext fun _ => rfl
    rw [this]
    exact (congrArg Spec.map (CommRingCat.ofHom_id)).trans (Spec.map_id _)
  have hs : x' ≫ pullback.snd _ _ = spMap ((algebraMap L₀ L).comp io') := by
    have h := congrArg (· ≫ pullback.snd _ _) hx'
    simp only [Category.assoc, hr2, pullback.lift_snd, z'] at h
    rw [hid, Category.comp_id] at h
    rw [h, Formalism.L2.PjFree.spMap_comp']
  have hf : x' ≫ pullback.fst _ _ ≫ r = spMap (algebraMap T.Fr L) ≫ x := by
    have h := congrArg (· ≫ pullback.fst _ _) hx'
    simp only [Category.assoc, hr1, pullback.lift_fst, z'] at h
    rw [h, ← Category.assoc, Formalism.L2.PjFree.spMap_comp']
  refine ⟨c₂, la₂, T', iT, φ, e', io₂, e₂, spMap ψ.toRingHom ≫ x' ≫ pullback.fst _ _, r, m, he', hv, hφ, ho₂,
    ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc x', hs, ← Category.assoc,
      Formalism.L2.PjFree.spMap_comp', Formalism.L2.PjFree.spMap_comp']
  · rw [Category.assoc, Category.assoc, hf, ← Category.assoc, Formalism.L2.PjFree.spMap_comp']
    have hc : ψ.toRingHom.comp (algebraMap T.Fr L) = iT := RingHom.ext fun a => hψ a
    rw [hc]

end GlobalTheory.LevelLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulDescendsNearClosedFibreOfEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Near.law_of_emb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → N.Law := by
  intro R _ _ _ hR M G' _ _ _ E N fU l hl1 hl2
  obtain ⟨hNoeth, -, hIC, -⟩ := hR
  obtain ⟨hbij, hsurj⟩ := _root_.GlobalTheory.Mum.Modif.appTop_bijective_surjective R M
  haveI := M.proper
  haveI := M.integral
  haveI := N.smooth
  obtain ⟨O, h, hfib, hover, hpt⟩ := _root_.GlobalTheory.Mum.Near.exists_mul_pt_pullback R M G' N
  have hconst := _root_.GlobalTheory.Mum.Near.closed_fibre_constant R M G' E N fU l hl1 hl2 hsurj O h hpt
  have hflat : Flat (N.U ⊗ N.U).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have hPB : IsPullback (pullback.fst (N.U ⊗ N.U).hom M.π) (pullback.snd (N.U ⊗ N.U).hom M.π) (N.U ⊗ N.U).hom M.π :=
    IsPullback.of_hasPullback _ _
  have hpsurj : Surjective (pullback.fst (N.U ⊗ N.U).hom M.π) := by
    haveI : Surjective M.π := hsurj
    infer_instance
  have key : ∀ i : {y₀ : (N.U ⊗ N.U).left // (N.U ⊗ N.U).hom y₀ = closedPoint R},
      ∃ (V : (N.U ⊗ N.U).left.Opens) (hV : pullback.fst (N.U ⊗ N.U).hom M.π ⁻¹ᵁ V ≤ O) (h₀ : V.toScheme ⟶ N.U.left),
        i.1 ∈ V ∧ (pullback.fst (N.U ⊗ N.U).hom M.π ∣_ V) ≫ h₀ = (pullback (N.U ⊗ N.U).hom M.π).homOfLE hV ≫ h := by
    rintro ⟨y₀, hy₀⟩
    obtain ⟨z, hz⟩ := hpsurj.surj y₀
    have hzO : z ∈ O := hfib z (by rw [hz]; exact hy₀)
    exact _root_.GlobalTheory.MorDesc.morphism_descends R M.S _ _ N.U.left M.π _ _ _ M.proper hsurj hbij hflat hPB O h y₀ (h ⟨z, hzO⟩)
      (fun z' hz' => hfib z' (by rw [hz']; exact hy₀))
      (fun z' hz' => hconst z' ⟨z, hzO⟩ (by rw [hz']; exact hz.symm) (by rw [hz']; exact hy₀))
  choose V hV h₀ hmem hcomm using key
  obtain ⟨hV', m, hm, huniq⟩ := _root_.GlobalTheory.MorDescent.descend_glue R M.S _ _ N.U.left M.π _ _ _ M.proper hsurj M.integral hflat hPB O h _ V hV h₀ hcomm
  refine ⟨⨆ i, V i, m, fun z hz => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hmem _⟩, ?_, ?_⟩
  · apply huniq
    simp only [reassoc_of% hm, hover, Scheme.homOfLE_ι_assoc, morphismRestrict_ι_assoc]
  · intro T v s x y hx hy
    have hc : (v ≫ (⨆ i, V i).ι) ≫ (N.U ⊗ N.U).hom = s ≫ M.π := by
      obtain ⟨x₀, h1, h2, -⟩ := hx
      have e1 : (fst N.U N.U).left ≫ N.U.hom = (N.U ⊗ N.U).hom := Over.w _
      simp only [← e1, ← h2, Category.assoc, ← pullback.condition]
      rw [reassoc_of% h1]
    let z : T ⟶ pullback (N.U ⊗ N.U).hom M.π := pullback.lift (v ≫ (⨆ i, V i).ι) s hc
    let z₁ := (isPullback_morphismRestrict (pullback.fst (N.U ⊗ N.U).hom M.π) (⨆ i, V i)).lift v z (pullback.lift_fst _ _ _).symm
    have hz₁a : z₁ ≫ (pullback.fst (N.U ⊗ N.U).hom M.π ∣_ ⨆ i, V i) = v := IsPullback.lift_fst _ _ _ _
    have hz₁b : z₁ ≫ (pullback.fst (N.U ⊗ N.U).hom M.π ⁻¹ᵁ ⨆ i, V i).ι = z := IsPullback.lift_snd _ _ _ _
    let t := z₁ ≫ (pullback (N.U ⊗ N.U).hom M.π).homOfLE hV'
    have ht : t ≫ O.ι = z := by
      simp only [t, Category.assoc, Scheme.homOfLE_ι, hz₁b]
    have hvm : v ≫ m = t ≫ h := by rw [← hz₁a, Category.assoc, hm, Category.assoc]
    rw [hvm]
    refine hpt T t s x y (by rw [reassoc_of% ht, pullback.lift_snd]) ?_ ?_
    · rw [reassoc_of% ht, pullback.lift_fst_assoc]; exact hx
    · rw [reassoc_of% ht, pullback.lift_fst_assoc]; exact hy

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPullOfRigOfSym
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymMulPull

open GlobalTheory.MulPull

section Base

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem hasGen_theta (hC : GlobalTheory.Published.CubeTheorem) (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) :
    HasGen L (thφ A (x3 A)) thε := by
  have := hA.comm
  obtain ⟨t, ht⟩ := hC S A hA L hL _ (x3 A 0) (x3 A 1) (x3 A 2)
  obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := thφ A (x3 A)) (ε' := thε) (fun U _ h => by
    have e := prod_cub (x3 A 0) (x3 A 1) (x3 A 2) h
    have i : lift (x3 A 0) (lift (x3 A 1) (x3 A 2)) = 𝟙 _ := by ext <;> simp [x3]
    rw [i] at e
    simp only [Over.id_left, Category.id_comp] at e
    rw [e, Fin.prod_univ_eight]
    simp only [Matrix.cons_val, zpow_one, zpow_neg]) t ht
  exact ⟨t', ht'⟩

end Base

end GlobalTheory.SymMulPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultilinearQuadraticIsHomogeneous
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem multilinear_quadratic_isHomogeneous : ∀ (P : Type) [AddCommGroup P] (g n : ℕ) (M : (Fin g → P) →ₘₗ[ℤ] ℤ) (a : Fin n → Fin n → P), ∃ F : MvPolynomial (Fin n) ℤ, F.IsHomogeneous (2 * g) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval m F = M (fun _ => ∑ i, ∑ j, (m i * m j) • a i j) := by
  intro P _ g n M a
  refine ⟨∑ r : Fin g → Fin n × Fin n, MvPolynomial.C (M (fun k => a (r k).1 (r k).2)) *
      ∏ k, (MvPolynomial.X (r k).1 * MvPolynomial.X (r k).2), ?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum
    intro r _
    have hX : ∀ k, (MvPolynomial.X (R := ℤ) (r k).1 * MvPolynomial.X (r k).2).IsHomogeneous 2 :=
      fun k => (MvPolynomial.isHomogeneous_X ℤ _).mul (MvPolynomial.isHomogeneous_X ℤ _)
    have h := (MvPolynomial.isHomogeneous_C (Fin n) (M fun k => a (r k).1 (r k).2)).mul
      (MvPolynomial.IsHomogeneous.prod Finset.univ _ (fun _ => 2) (fun k _ => hX k))
    convert h using 1
    simp [mul_comm]
  · intro m
    have hx : (fun _ : Fin g => ∑ i, ∑ j, (m i * m j) • a i j) =
        fun _ => ∑ p : Fin n × Fin n, (m p.1 * m p.2) • a p.1 p.2 := by
      funext _; exact (Fintype.sum_prod_type' (fun i j => (m i * m j) • a i j)).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, MultilinearMap.map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]
    simp only [RingHom.id_apply]

end GlobalTheory
end

