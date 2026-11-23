module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0530
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0552
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0558
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0577
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.GrowForms
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0556
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0561
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0527
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcat
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityChartIntegralFormula
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

theorem onePiece {Y : Type} {D : ℕ} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (m : Measure Y) (e : OpenPartialHomeomorph Y (Fin D → ℂ)) (r : (Fin D → ℂ) → ℝ)
    (hr : ContinuousOn r e.target)
    (hm : m.restrict e.source = ((volume.restrict e.target).withDensity fun v =>
      ENNReal.ofReal (r v)).map e.symm)
    (S : Set Y) (hS : MeasurableSet S) (hSs : S ⊆ e.source) (K : Y → ℝ)
    (hK : IntegrableOn K S m) :
    Integrable ((e '' S).indicator fun v => K (e.symm v) * max (r v) 0) ∧
      ∫ y in S, K y ∂m = ∫ v, (e '' S).indicator (fun v => K (e.symm v) * max (r v) 0) v := by
  classical
  set ν0 : Measure (Fin D → ℂ) := volume.restrict e.target with hν0
  set d : (Fin D → ℂ) → ENNReal := fun v => ENNReal.ofReal (r v) with hd
  have htm : MeasurableSet e.target := e.open_target.measurableSet
  have hsm : MeasurableSet e.source := e.open_source.measurableSet
  have hdm : AEMeasurable d ν0 :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hr.aemeasurable htm)
  have hdlt : ∀ᵐ v ∂ν0, d v < ⊤ := Filter.Eventually.of_forall fun v => ENNReal.ofReal_lt_top
  have hsy0 : AEMeasurable e.symm ν0 := e.continuousOn_symm.aemeasurable htm
  have hsy : AEMeasurable e.symm (ν0.withDensity d) :=
    hsy0.mono_ac (withDensity_absolutelyContinuous _ _)
  set K' : Y → ℝ := S.indicator K with hK'
  have hK1 : Integrable K' m := (integrable_indicator_iff hS).2 hK
  have hK2 : Integrable K' ((ν0.withDensity d).map e.symm) := by
    rw [← hm]; exact hK1.restrict
  have hK3 : Integrable (K' ∘ e.symm) (ν0.withDensity d) :=
    (integrable_map_measure hK2.aestronglyMeasurable hsy).1 hK2
  have hK4 : Integrable (fun v => (d v).toReal • (K' ∘ e.symm) v) ν0 :=
    (integrable_withDensity_iff_integrable_smul₀' hdm hdlt).1 hK3
  have hfun : (e '' S).indicator (fun v => K (e.symm v) * max (r v) 0) =
      e.target.indicator (fun v => (d v).toReal • (K' ∘ e.symm) v) := by
    funext v
    by_cases hv : v ∈ e '' S
    · obtain ⟨y, hy, rfl⟩ := hv
      have hyt : e y ∈ e.target := e.map_source (hSs hy)
      have hinv : e.symm (e y) = y := e.left_inv (hSs hy)
      rw [Set.indicator_of_mem (Set.mem_image_of_mem _ hy), Set.indicator_of_mem hyt]
      simp [hinv, hK', hy, hd, ENNReal.toReal_ofReal', mul_comm]
    · rw [Set.indicator_of_notMem hv]
      by_cases hvt : v ∈ e.target
      · have hns : e.symm v ∉ S := fun h => hv ⟨_, h, e.right_inv hvt⟩
        rw [Set.indicator_of_mem hvt]; simp [hK', hns]
      · rw [Set.indicator_of_notMem hvt]
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact (integrable_indicator_iff htm).2 hK4
  · rw [hfun, integral_indicator htm]
    calc ∫ y in S, K y ∂m = ∫ y, K' y ∂m := (integral_indicator hS).symm
      _ = ∫ y in e.source, K' y ∂m := by
          refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
          intro y hy
          exact Set.indicator_of_notMem (fun h => hy (hSs h)) _
      _ = ∫ y, K' y ∂((ν0.withDensity d).map e.symm) := by rw [hm]
      _ = ∫ v, (K' ∘ e.symm) v ∂(ν0.withDensity d) :=
          integral_map hsy hK2.aestronglyMeasurable
      _ = ∫ v, (d v).toReal • (K' ∘ e.symm) v ∂ν0 :=
          integral_withDensity_eq_integral_toReal_smul₀ hdm hdlt _

theorem exists_partition {Y ι : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [Countable ι] (U : ι → Set Y) (hU : ∀ l, IsOpen (U l)) (G : Set Y) (hG : MeasurableSet G)
    (hGs : G ⊆ ⋃ l, U l) :
    ∃ S : ι → Set Y, (∀ l, MeasurableSet (S l)) ∧ (∀ l, S l ⊆ U l) ∧
      Pairwise (Function.onFun Disjoint S) ∧ ⋃ l, S l = G := by
  classical
  haveI := Encodable.ofCountable ι
  refine ⟨fun l => (G ∩ U l) \ ⋃ (k : ι) (_ : Encodable.encode k < Encodable.encode l), U k,
    fun l => ?_, fun l y hy => hy.1.2, ?_, ?_⟩
  · exact (hG.inter (hU l).measurableSet).diff
      (isOpen_iUnion fun k => isOpen_iUnion fun _ => hU k).measurableSet
  · have key : ∀ l k : ι, Encodable.encode k < Encodable.encode l →
        Disjoint ((G ∩ U k) \ ⋃ (j : ι) (_ : Encodable.encode j < Encodable.encode k), U j)
          ((G ∩ U l) \ ⋃ (j : ι) (_ : Encodable.encode j < Encodable.encode l), U j) := by
      intro l k hlt
      refine Set.disjoint_left.2 fun y hyk hyl => hyl.2 ?_
      exact Set.mem_iUnion₂.2 ⟨k, hlt, hyk.1.2⟩
    intro l k hne
    rcases lt_trichotomy (Encodable.encode l) (Encodable.encode k) with h | h | h
    · exact key k l h
    · exact absurd (Encodable.encode_injective h) hne
    · exact (key l k h).symm
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun l y hy => hy.1.1
    · intro y hy
      have hex : ∃ n, ∃ l : ι, Encodable.encode l = n ∧ y ∈ U l := by
        obtain ⟨l, hl⟩ := Set.mem_iUnion.1 (hGs hy)
        exact ⟨_, l, rfl, hl⟩
      obtain ⟨l, hl, hyl⟩ := Nat.find_spec hex
      refine Set.mem_iUnion.2 ⟨l, ⟨hy, hyl⟩, fun hmem => ?_⟩
      obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 hmem
      exact Nat.find_min hex (hl ▸ hk) ⟨k, rfl, hyk⟩

theorem abs_eq_max_add_max (a : ℝ) : |a| = max a 0 + max (-a) 0 := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring

theorem integral_pieces : ∀ {Y ι : Type} {D : ℕ} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Countable ι]
    (μ : ℤˣ → Measure Y) (e : ι → OpenPartialHomeomorph Y (Fin D → ℂ)) (ρ : ι → (Fin D → ℂ) → ℝ),
    (∀ l, ContinuousOn (ρ l) (e l).target) →
    (∀ l (ε : ℤˣ), (μ ε).restrict (e l).source = ((volume.restrict (e l).target).withDensity fun v =>
      ENNReal.ofReal (((ε : ℤ) : ℝ) * ρ l v)).map (e l).symm) →
    ∀ (G : Set Y), MeasurableSet G → G ⊆ ⋃ l, (e l).source → ∀ F : Y → ℝ, (∀ ε, IntegrableOn F G (μ ε)) →
    ∃ S : ι → Set Y, (∀ l, MeasurableSet (S l)) ∧ (∀ l, S l ⊆ (e l).source) ∧ Pairwise (Function.onFun Disjoint S) ∧
      ⋃ l, S l = G ∧ ∫ y in G, F y ∂μ 1 - ∫ y in G, F y ∂μ (-1) =
        ∫ v, ∑' l, ((e l) '' S l).indicator (fun v => F ((e l).symm v) * ρ l v) v := by
  intro Y ι D _ _ _ _ μ e ρ hρ hμ G hG hGs F hF
  obtain ⟨S, hSm, hSs, hSd, hSu⟩ := exists_partition (fun l => (e l).source)
    (fun l => (e l).open_source) G hG hGs
  refine ⟨S, hSm, hSs, hSd, hSu, ?_⟩
  have hSG : ∀ l, S l ⊆ G := fun l => hSu ▸ Set.subset_iUnion S l
  have piece : ∀ (l : ι) (ε : ℤˣ) (K : Y → ℝ), IntegrableOn K (S l) (μ ε) →
      Integrable ((e l '' S l).indicator fun v => K ((e l).symm v) * max (((ε : ℤ) : ℝ) * ρ l v) 0) ∧
      ∫ y in S l, K y ∂μ ε =
        ∫ v, (e l '' S l).indicator (fun v => K ((e l).symm v) * max (((ε : ℤ) : ℝ) * ρ l v) 0) v :=
    fun l ε K hK => onePiece (μ ε) (e l) (fun v => ((ε : ℤ) : ℝ) * ρ l v)
      (continuousOn_const.mul (hρ l)) (hμ l ε) (S l) (hSm l) (hSs l) K hK
  set Φ : ι → (Fin D → ℂ) → ℝ := fun l =>
    (e l '' S l).indicator (fun v => F ((e l).symm v) * ρ l v) with hΦ
  have hΦsub : ∀ l, Φ l =
      (e l '' S l).indicator (fun v => F ((e l).symm v) * max ((((1 : ℤˣ) : ℤ) : ℝ) * ρ l v) 0) -
      (e l '' S l).indicator (fun v => F ((e l).symm v) * max ((((-1 : ℤˣ) : ℤ) : ℝ) * ρ l v) 0) := by
    intro l
    funext v
    by_cases hv : v ∈ e l '' S l
    · simp only [hΦ, Pi.sub_apply, Set.indicator_of_mem hv]
      have h := max_zero_sub_max_neg_zero_eq_self (ρ l v)
      simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_mul]
      rw [← mul_sub, h]
    · simp [hΦ, Set.indicator_of_notMem hv]
  have hΦnorm : ∀ l v, ‖Φ l v‖ =
      (e l '' S l).indicator (fun v => ‖F ((e l).symm v)‖ * max ((((1 : ℤˣ) : ℤ) : ℝ) * ρ l v) 0) v +
      (e l '' S l).indicator (fun v => ‖F ((e l).symm v)‖ * max ((((-1 : ℤˣ) : ℤ) : ℝ) * ρ l v) 0) v := by
    intro l v
    by_cases hv : v ∈ e l '' S l
    · simp only [hΦ, Set.indicator_of_mem hv]
      simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_mul]
      rw [norm_mul, ← mul_add, Real.norm_eq_abs (ρ l v), abs_eq_max_add_max]
    · simp [hΦ, Set.indicator_of_notMem hv]
  have hFS : ∀ l ε, IntegrableOn F (S l) (μ ε) := fun l ε => (hF ε).mono_set (hSG l)
  have hFnS : ∀ l ε, IntegrableOn (fun y => ‖F y‖) (S l) (μ ε) := fun l ε => (hFS l ε).norm
  have hΦint : ∀ l, Integrable (Φ l) := by
    intro l
    rw [hΦsub l]
    exact (piece l 1 F (hFS l 1)).1.sub (piece l (-1) F (hFS l (-1))).1
  have hΦval : ∀ l, ∫ v, Φ l v = ∫ y in S l, F y ∂μ 1 - ∫ y in S l, F y ∂μ (-1) := by
    intro l
    rw [hΦsub l, (piece l 1 F (hFS l 1)).2, (piece l (-1) F (hFS l (-1))).2]
    exact integral_sub (piece l 1 F (hFS l 1)).1 (piece l (-1) F (hFS l (-1))).1
  have hΦnval : ∀ l, ∫ v, ‖Φ l v‖ =
      ∫ y in S l, ‖F y‖ ∂μ 1 + ∫ y in S l, ‖F y‖ ∂μ (-1) := by
    intro l
    simp only [hΦnorm l]
    rw [(piece l 1 _ (hFnS l 1)).2, (piece l (-1) _ (hFnS l (-1))).2]
    exact integral_add (piece l 1 _ (hFnS l 1)).1 (piece l (-1) _ (hFnS l (-1))).1
  have hU : ∀ ε, IntegrableOn F (⋃ l, S l) (μ ε) := fun ε => by rw [hSu]; exact hF ε
  have hsumN : ∀ ε, Summable fun l => ∫ y in S l, ‖F y‖ ∂μ ε := fun ε =>
    (hasSum_integral_iUnion hSm hSd (hU ε).norm).summable
  have h1 : HasSum (fun l => ∫ v, Φ l v) (∫ v, ∑' l, Φ l v) :=
    hasSum_integral_of_summable_integral_norm hΦint
      (by simp only [hΦnval]; exact (hsumN 1).add (hsumN (-1)))
  have h2 : HasSum (fun l => ∫ y in S l, F y ∂μ 1 - ∫ y in S l, F y ∂μ (-1))
      (∫ y in G, F y ∂μ 1 - ∫ y in G, F y ∂μ (-1)) := by
    have a := hasSum_integral_iUnion hSm hSd (hU 1)
    have b := hasSum_integral_iUnion hSm hSd (hU (-1))
    rw [hSu] at a b
    exact a.sub b
  simp only [hΦval] at h1
  exact h2.unique h1

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCosetTwistedConjugacy
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SuppCent

theorem comm_of_conj {G : Type} [Group G] (γ p₀ q : G)
    (h : q⁻¹ * (p₀⁻¹ * γ * p₀) * q = p₀⁻¹ * γ * p₀) :
    (p₀ * q * p₀⁻¹) * γ = γ * (p₀ * q * p₀⁻¹) := by
  calc (p₀ * q * p₀⁻¹) * γ = p₀ * q * (p₀⁻¹ * γ * p₀) * p₀⁻¹ := by group
    _ = p₀ * q * (q⁻¹ * (p₀⁻¹ * γ * p₀) * q) * p₀⁻¹ := by rw [h]
    _ = γ * (p₀ * q * p₀⁻¹) := by group

theorem conj_comm {G : Type} [Group G] (γ p₀ t : G) (h : t * γ = γ * t) :
    (p₀⁻¹ * t * p₀)⁻¹ * (p₀⁻¹ * γ * p₀) * (p₀⁻¹ * t * p₀) = p₀⁻¹ * γ * p₀ := by
  calc _ = p₀⁻¹ * t⁻¹ * (γ * t) * p₀ := by group
    _ = p₀⁻¹ * t⁻¹ * (t * γ) * p₀ := by rw [h]
    _ = _ := by group

theorem isCompact_closure_zpowers_conj {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] (c t : G)
    (h : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    IsCompact (closure (Subgroup.zpowers (c⁻¹ * t * c) : Set G)) := by
  have hφ : Continuous fun x : G => c⁻¹ * x * c := by fun_prop
  have hK := h.image hφ
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro _ ⟨k, rfl⟩
  refine ⟨t ^ k, subset_closure (Subgroup.zpow_mem_zpowers t k), ?_⟩
  have e : c⁻¹ * t * c = MulAut.conj c⁻¹ t := by simp [MulAut.conj_apply]
  have e' : ∀ x : G, c⁻¹ * x * c = MulAut.conj c⁻¹ x := fun x => by simp [MulAut.conj_apply]
  simp only [e', map_zpow]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → (∀ (y : Fin n → ℤ), StrictAnti y → ∀ δ : GLw n w, dcos n w (tdiag ϖ y) δ ≠ 0 → ∃ m ∈ iwGL n w, ∃ τ : GLw n w, ((∀ i j : Fin n, i ≠ j → τ.val i j = 0) ∧ ∀ i, Valued.v (τ.val i i) = 1) ∧ m⁻¹ * δ * m = tdiag ϖ y * τ) → ∀ γ : UL n w, (∃ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0) → ∃ (p₀ : UL n w) (u : Fin n → (w.adicCompletion E)ˣ), (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) ∧ (p₀⁻¹ * γ * p₀).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ ∧ (∀ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0 ↔ ∃ z ∈ twCent (MonoidHom.id (UL n w)) γ, ∃ i ∈ iwU n w b, p = z * p₀ * i) ∧ cptPart (twCent (MonoidHom.id (UL n w)) γ) = twCent (MonoidHom.id (UL n w)) γ ⊓ (iwU n w b).map (MulAut.conj p₀).toMonoidHom := by
  intro E _ _ _ hU w hw n b hb ϖ hϖ l hl hyp γ ⟨p1, hp1⟩
  obtain ⟨hW1, hW2, hWc, -⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  have hinj : Function.Injective (wexp n l) :=
    (GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl).1.injective
  have huc := GlobalTheory.CompanionTheory.UnitaryContraction.main E hU w hw n b hb ϖ hϖ l hl hyp
  obtain ⟨m, hm, u, hu, hmu⟩ := huc _ hp1
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : UL n w, p₀ = p1 * m := ⟨_, rfl⟩
  have hγ0 : (p₀⁻¹ * γ * p₀).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ := by
    rw [← hmu]
    congr 1
    rw [hp₀]
    group

  have key : ∀ (q : UL n w) (u' : Fin n → (w.adicCompletion E)ˣ),
      (∀ i, ordL (u' i : w.adicCompletion E) = wexp n l i) →
      (q⁻¹ * (p₀⁻¹ * γ * p₀) * q).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u' * b⁻¹ →
      u = u' ∧ ∃ s : Fin n → (w.adicCompletion E)ˣ,
        q.1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * b⁻¹ := by
    intro q u' hu' e
    have e' : q.1⁻¹ * (b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹) * q.1 =
        b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u' * b⁻¹ := by
      rw [← hγ0, ← e]
      rfl
    have hh : (b⁻¹ * q.1 * b)⁻¹ * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * (b⁻¹ * q.1 * b) =
        GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u' := by
      calc _ = b⁻¹ * (q.1⁻¹ * (b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹) * q.1) * b := by
            group
        _ = _ := by rw [e']; group
    obtain ⟨h1, s, hs⟩ := GlobalTheory.CompanionTheory.DiagRigid.diag_rigid (w.adicCompletion E) n (wexp n l) hinj u u'
      hu hu' _ hh
    refine ⟨h1, s, ?_⟩
    rw [← hs]
    group
  refine ⟨p₀, u, hu, hγ0, fun p => ⟨fun hp => ?_, ?_⟩, ?_⟩
  ·
    obtain ⟨m', hm', u', hu', e⟩ := huc _ hp
    have e2 : (p₀⁻¹ * p * m')⁻¹ * (p₀⁻¹ * γ * p₀) * (p₀⁻¹ * p * m') = m'⁻¹ * (p⁻¹ * γ * p) * m' := by
      group
    obtain ⟨rfl, -⟩ := key (p₀⁻¹ * p * m') u' hu' (by rw [e2]; exact e)
    have hq : (p₀⁻¹ * p * m')⁻¹ * (p₀⁻¹ * γ * p₀) * (p₀⁻¹ * p * m') = p₀⁻¹ * γ * p₀ := by
      apply Subtype.ext
      rw [e2, e, hγ0]
    refine ⟨p₀ * (p₀⁻¹ * p * m') * p₀⁻¹, comm_of_conj γ p₀ _ hq, m'⁻¹, inv_mem hm', ?_⟩
    group
  ·
    rintro ⟨z, hz, i, hi, rfl⟩
    have hz' : z * γ = γ * z := hz
    have e : (z * p₀ * i)⁻¹ * γ * (z * p₀ * i) = i⁻¹ * (p₀⁻¹ * γ * p₀) * i := by
      calc _ = i⁻¹ * p₀⁻¹ * z⁻¹ * (γ * z) * p₀ * i := by group
        _ = i⁻¹ * p₀⁻¹ * z⁻¹ * (z * γ) * p₀ * i := by rw [hz']
        _ = _ := by group
    rw [e, GlobalTheory.CompanionTheory.DiagCoset.fU_diag E hU w hw n b hb ϖ hϖ l hl _ u hu hγ0 _ (inv_mem hi) _ hi]
    exact one_ne_zero
  ·
    refine GlobalTheory.CompanionTheory.CptGen.cptPart_eq_inf (UL n w) _ _ ?_ ?_
    · rw [Subgroup.coe_map]
      refine hWc.image ?_
      change Continuous fun x : UL n w => p₀ * x * p₀⁻¹
      fun_prop
    · intro t ht hc
      have ht' : t * γ = γ * t := ht
      obtain ⟨-, s, hs⟩ := key (p₀⁻¹ * t * p₀) u hu (by rw [conj_comm γ p₀ t ht']; exact hγ0)
      have hv := GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers E w n (UL n w)
        (p₀⁻¹ * t * p₀) b s hs (isCompact_closure_zpowers_conj p₀ t hc)
      have hmem : p₀⁻¹ * t * p₀ ∈ iwU n w b := by
        rw [hW2]
        have : b⁻¹ * (p₀⁻¹ * t * p₀).1 * b = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s := by
          rw [hs]
          group
        rw [this]
        exact GlobalTheory.CompanionTheory.DiagCoset.diagT_mem_iwGL w n s hv
      refine Subgroup.mem_map.2 ⟨_, hmem, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]

end GlobalTheory.CompanionTheory.SuppCent
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHalfHolds
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CompanionTheory.SiegelEisHalf

theorem eisHalf : EisHalf := by
  unfold SiegelEisensteinSeries.EisHalf
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY χ hχ c hc b K a hb hK ha s₁ f hf
  obtain ⟨Ê, t₁, hsum, hdiff⟩ := GlobalTheory.T.eisenstein_series_continuation F E σ B n Y r s hB hn hY b K a hb hK ha χ s₁ f hf
  obtain ⟨t₀, h23⟩ := GlobalTheory.T.eisenstein_vertical_bound F E σ B n Y r s hB hn hY b K a hb hK ha χ s₁ f hf
  obtain ⟨t, ht₀, ht₁⟩ : ∃ t : ℝ, t₀ ≤ t ∧ t₁ ≤ t := ⟨max t₀ t₁, le_max_left _ _, le_max_right _ _⟩
  have hsum' : ∀ z : ℂ, t < z.re → ∀ x : GlobalTheory.ThK.Dbl.G2 σ Y,
      HasSum (GlobalTheory.ThK.Dbl.eisTerm (GlobalTheory.ThK.Dbl.flat a f s₁ z) x) (Ê z x) :=
    fun z hz x => hsum z (lt_of_le_of_lt ht₁ hz) x
  obtain ⟨hmod, hcont, hbd⟩ := h23 t Ê ht₀ hsum'
  let v : ℂ → ↥(GlobalTheory.ThK.Dbl.modFun σ Y) := fun z =>
    if hz : t < z.re then ⟨fun x => Ê z x, hmod z hz⟩ else 0
  have hv : ∀ z : ℂ, t < z.re → ∀ x : GlobalTheory.ThK.Dbl.G2 σ Y,
      (↑(v z) : GlobalTheory.ThK.Dbl.G2 σ Y → ℂ) x = Ê z x := by
    intro z hz x
    simp only [v]
    rw [dite_eq_left hz]
  refine ⟨t, v, fun z hz x => by rw [hv z hz x]; exact hsum' z hz x, ?_⟩
  have hS : IsOpen {z : ℂ | t < z.re} := isOpen_lt continuous_const Complex.continuous_re
  apply GlobalTheory.CompanionTheory.WeakHolo.wholo_growForms v hS
  · intro x
    exact ((hdiff x).mono fun z hz => lt_of_le_of_lt ht₁ hz).congr fun z hz => hv z hz x
  · exact hcont.congr fun y hy => hv y.1 hy.1 y.2
  · intro Q hQS hQ
    rcases Q.eq_empty_or_nonempty with hQe | hne
    · exact ⟨0, 0, fun z hz => by simp [hQe] at hz⟩
    · obtain ⟨z₀, hz₀, hmin⟩ := hQ.exists_isMinOn hne Complex.continuous_re.continuousOn
      obtain ⟨z₁, _, hmax⟩ := hQ.exists_isMaxOn hne Complex.continuous_re.continuousOn
      obtain ⟨C, N, hC⟩ := hbd z₀.re z₁.re (hQS hz₀)
      refine ⟨C, N, fun z hz x => ?_⟩
      rw [hv z (hQS hz) x]
      exact hC z (isMinOn_iff.mp hmin z hz) (isMaxOn_iff.mp hmax z hz) x

end GlobalTheory.CompanionTheory.SiegelEisHalf

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConjEqOnAlgebraicClosure
section
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

noncomputable section

namespace GlobalTheory.CompanionTheory.EllipticCM

theorem exists_conj_eq_on_algebraicClosure {K : Type} [Field K] [Algebra K ℂ]
    (σ : ℂ ≃ₐ[K] ℂ) (ι : AlgebraicClosure K →ₐ[K] ℂ)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hσ : ∀ x, σ (ι x) = ι (g x))
    (e : algebraicClosure K ℂ ≃ₐ[K] AlgebraicClosure K) :
    ∃ ρ : algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ,
      ∀ y : algebraicClosure K ℂ,
        (((ρ * ((e.trans g).trans e.symm) * ρ⁻¹) y : algebraicClosure K ℂ) : ℂ) = σ (y : ℂ) := by
  let ι' : algebraicClosure K ℂ →ₐ[K] ℂ := ι.comp (e : algebraicClosure K ℂ →ₐ[K] AlgebraicClosure K)
  have hmem : ∀ y, ι' y ∈ (algebraicClosure K ℂ).toSubalgebra := fun y =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic y).algHom ι')
  let ρ₀ : algebraicClosure K ℂ →ₐ[K] algebraicClosure K ℂ :=
    ι'.codRestrict (algebraicClosure K ℂ).toSubalgebra hmem
  let ρ : algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ :=
    AlgEquiv.ofBijective ρ₀ (Algebra.IsAlgebraic.algHom_bijective ρ₀)
  have hρ : ∀ w, ((ρ w : algebraicClosure K ℂ) : ℂ) = ι (e w) := fun _ => rfl
  refine ⟨ρ, fun y => ?_⟩
  obtain ⟨z, rfl⟩ := ρ.surjective y
  have h1 : (ρ * ((e.trans g).trans e.symm) * ρ⁻¹) (ρ z) = ρ (e.symm (g (e z))) := by
    simp [AlgEquiv.mul_apply, AlgEquiv.aut_inv]
  rw [h1, hρ, hρ, hσ, AlgEquiv.apply_symm_apply]

theorem exists_globalArtinMap_tied : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K ℂ], Module.finrank ℚ K = 2 → ∃ Art₀ : Neutral.B1.IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K, Neutral.B1.IsGlobalArtinMap K Art₀ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (s : Neutral.B1.Ideles K), GlobalTheory.EllipticCM.RestrictsTo σ (Art₀ (QuotientGroup.mk s)) → ∀ x : GroundTheory.LocalField.maximalAbelianExtension K (algebraicClosure K ℂ), ((GroundTheory.Global.artinMap K (algebraicClosure K ℂ) (GroundTheory.Global.IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) = σ ((x : algebraicClosure K ℂ) : ℂ) := by
  intro K _ _ _ _ _
  let e : algebraicClosure K ℂ ≃ₐ[K] AlgebraicClosure K := IsAlgClosure.equiv K _ _
  obtain ⟨Art, hArt, hArtσ⟩ := GlobalTheory.LatVal.exists_globalArtinMap
    (CompanionTheory.FamInh.isGlobalArtin_inv (E := K) (Ω := algebraicClosure K ℂ)) e
  obtain ⟨φ, -, hφb, hφ⟩ := GlobalTheory.HeckeGal.exists_abMap_of_algEquiv e
  refine ⟨Art, hArt, ?_⟩
  rintro σ s ⟨ι, g, hσ, hg⟩ x
  obtain ⟨ρ, hρ⟩ := exists_conj_eq_on_algebraicClosure σ ι g hσ e
  obtain ⟨τ, hτ⟩ := GlobalTheory.HeckeGal.toAb_surjective (E := K) (Ω := algebraicClosure K ℂ)
    (CompanionTheory.FamInh.art0 K (algebraicClosure K ℂ) s)
  have h1 : Art (QuotientGroup.mk s) = Neutral.B1.toAb K ((e.symm.trans τ).trans e) :=
    hArtσ s τ (by rw [hτ, MonoidHom.inv_apply, inv_inv])
  have h2 : (e.symm.trans ((e.trans g).trans e.symm)).trans e = g := by
    ext y
    simp
  have h3 : GlobalTheory.HeckeGal.toAb K (algebraicClosure K ℂ) ((e.trans g).trans e.symm) =
      GlobalTheory.HeckeGal.toAb K (algebraicClosure K ℂ) τ :=
    hφb.1 (by rw [hφ, hφ, h2, hg, h1])
  have h4 : GlobalTheory.HeckeGal.toAb K (algebraicClosure K ℂ) (ρ * ((e.trans g).trans e.symm) * ρ⁻¹) =
      CompanionTheory.FamInh.art0 K (algebraicClosure K ℂ) s := by
    rw [map_mul, map_mul, map_inv, h3, hτ, mul_comm (GlobalTheory.HeckeGal.toAb K _ ρ), mul_inv_cancel_right]
  have h5 := GroundTheory.LocalField.topologicalAbelianizationEquiv_mk_apply K (algebraicClosure K ℂ)
    (ρ * ((e.trans g).trans e.symm) * ρ⁻¹) x
  have h6 : GroundTheory.LocalField.topologicalAbelianizationEquiv K (algebraicClosure K ℂ)
      (((ρ * ((e.trans g).trans e.symm) * ρ⁻¹ : algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ)) :
        TopologicalAbelianization (algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ)) =
      GroundTheory.Global.artinMap K (algebraicClosure K ℂ) (GroundTheory.Global.IdeleClassGroup.mk K s) := by
    refine Eq.trans (congrArg (GroundTheory.LocalField.topologicalAbelianizationEquiv K (algebraicClosure K ℂ)) h4) ?_
    exact (GroundTheory.LocalField.topologicalAbelianizationEquiv K (algebraicClosure K ℂ)).apply_symm_apply _
  rw [h6] at h5
  rw [h5, hρ]

end GlobalTheory.CompanionTheory.EllipticCM

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FramesSumInvariantUnderStabiliserStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_sum_invariant_under_stabiliser : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (w : UJ (σ : E →+* E) (hypOne J)), gact σ w (e0 E M) = e0 E M → ∀ f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞, ∑' X : framesOne σ J n, f (gact σ w X.1) = ∑' X : framesOne σ J n, f X.1 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_gact_framesOne | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_gact_framesOne | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_gact_framesOne <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcatStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_concat : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {s N : ℕ} (y : Fin s → IrrGL (k := k)) (hy : ∑ a, (y a).1 = N) (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) (hx : ∀ a, ∑ i, (x a i).1 = (y a).1) (hcat : ∑ i, (concat c x i).1 = N) (hpos : ∀ a, 1 ≤ jm (x a) (hx a) (y a).rep) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hfl : HasFiniteLength π), jm y hy π ≤ jm (concat c x) hcat π := by
  first | exact @GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat | exact GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat | (intros; apply GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat <;> assumption)
end

