module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0151
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0149
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0154
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0039
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationTopEqBot
section
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatNil

theorem isDPMorphism_ι {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)
    (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) :
    IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γB f ξ) (Lat.ι f ξ l M) := by
  refine ⟨Ideal.map_comap_le, ?_⟩
  intro n a ha
  exact (Lat.ι_γ f ξ l M hc ha).symm

theorem dividedPowerFiltration_eq_bot : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), pdP (Lat.γ f ξ l M hc) m = ⊥ := by
  intro W B _ _ _ f ξ l M m h hc
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  have h1 : Lat.ι f ξ l M x ∈ pdP (Lat.γB f ξ) m := dividedPowerFiltration_map (isDPMorphism_ι f ξ l M hc) m hx
  rw [GlobalTheory.T.divided_power_filtration_span_pow f ξ m, h.nil, Ideal.mem_span_singleton, zero_dvd_iff] at h1
  exact Lat.ι_injective f ξ l M (by rw [h1, map_zero])

end GlobalTheory.CompanionTheory.LatNil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeLPowMemSpanOfNotMem
section
set_option autoImplicit false

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Lat

private theorem exists_sub_iota_mem_of_sub_involution_mem {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (b : B) (hb : b ∈ Lat.sub f ξ l M) : ∃ w : W, f w - b ∈ Lat.IB f ξ := by
  have hη : Lat.η f ξ l M ∈ Lat.IB f ξ := by
    rw [Lat.η, Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hle : Lat.sub f ξ l M ≤
      (((Ideal.Quotient.mk (Lat.IB f ξ)).comp f).range).comap (Ideal.Quotient.mk (Lat.IB f ξ)) := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro y (⟨w, rfl⟩ | ⟨i, rfl⟩)
    · exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨w, rfl⟩)
    · cases i with
      | zero => exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨1, by simp [Lat.dpE]⟩)
      | succ i =>
        have hd : Lat.dpE f ξ l M (i + 1) ∈ Lat.IB f ξ := by
          rw [Lat.dpE, Algebra.smul_def, pow_succ']
          exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hη)
        refine Subring.mem_comap.2 (RingHom.mem_range.2 ⟨0, ?_⟩)
        rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
        exact hd
  obtain ⟨w, hw⟩ := RingHom.mem_range.1 (Subring.mem_comap.1 (hle hb))
  exact ⟨w, Ideal.Quotient.eq.1 hw⟩

theorem pow_mem_span_sup_I : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → ∀ x : Lat.A f ξ l M, x ∉ Lat.I f ξ l M →
      ∃ n : ℕ, (l : Lat.A f ξ l M) ^ n ∈ Ideal.span {x} ⊔ Lat.I f ξ l M := by
  intro W B _ _ _ f ξ l M m hH x hx
  have hxmem : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M := (show ↥(Lat.sub f ξ l M) from x).2
  obtain ⟨w, hw⟩ := exists_sub_iota_mem_of_sub_involution_mem f ξ l M _ hxmem
  have hxw : Lat.ofW f ξ l M w - x ∈ Lat.I f ξ l M := by
    show Lat.ι f ξ l M (Lat.ofW f ξ l M w - x) ∈ Lat.IB f ξ
    rw [map_sub, Lat.ι_ofW]
    exact hw
  have hξI : Lat.ofW f ξ l M ξ ∈ Lat.I f ξ l M := by
    show Lat.ι f ξ l M (Lat.ofW f ξ l M ξ) ∈ Lat.IB f ξ
    rw [Lat.ι_ofW]
    exact Ideal.mem_span_singleton_self _
  have hwnot : ¬ ξ ∣ w := by
    rintro ⟨v, rfl⟩
    apply hx
    have h1 : Lat.ofW f ξ l M (ξ * v) ∈ Lat.I f ξ l M := by
      rw [map_mul]
      exact Ideal.mul_mem_right _ _ hξI
    have h2 := (Lat.I f ξ l M).sub_mem h1 hxw
    simpa using h2
  have hq : Ideal.Quotient.mk (Ideal.span {ξ}) w ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hwnot
  obtain ⟨n, c, hc⟩ := hH.dv _ hq
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hmem : (l : W) ^ n - w * u ∈ Ideal.span {ξ} := by
    rw [← Ideal.Quotient.eq]
    simpa using hc
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨n, ?_⟩
  have e : (l : Lat.A f ξ l M) ^ n = Lat.ofW f ξ l M ((l : W) ^ n) := by
    rw [map_pow, map_natCast]
  rw [e, show (l : W) ^ n = w * u + v * ξ by rw [hv]; ring, map_add (f := _), map_mul, map_mul]
  refine Ideal.add_mem _ ?_ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ hξI))
  have e2 : Lat.ofW f ξ l M w * Lat.ofW f ξ l M u =
      x * Lat.ofW f ξ l M u + (Lat.ofW f ξ l M w - x) * Lat.ofW f ξ l M u := by ring
  rw [e2]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self x)))
    (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ hxw))

end GlobalTheory.CompanionTheory.Lat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBinaryGramIntegral
section
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FibreCpt

open GlobalTheory.CompanionTheory.SW.FibreRatio

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem masses_field (R : Type) [Field R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    [BorelSpace R] (hloc : IsLocR R) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hfib : IsGramFib R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m)
    (A : Set (Fin 1 → Fin M → R ⊗[F] E)) (hAc : IsCompact A) (hAo : IsOpen A)
    (hAU : A ⊆ {X | IsUnit (gramR R σ J X).det}) :
    Continuous (fun s : R => (m (hermScal R σ s) A).toReal) ∧
    HasCompactSupport (fun s : R => (m (hermScal R σ s) A).toReal) ∧
    ENNReal.ofReal (∫ s, (m (hermScal R σ s) A).toReal ∂lam) = coordW R b lam 1 M A := by
  obtain ⟨h1, h2, h3, h4, -⟩ := id hloc
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, hT2, -, htr, -, hBor, -, hgr⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ h R
  haveI := hT2
  haveI := hBor 1 M
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  have hHaar := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ h R d b lam hlam
  have hμ := hHaar.2.1 1 M
  have hν := hHaar.2.2 1
  have hAm : MeasurableSet A := hAo.measurableSet
  set φ : (Fin 1 → Fin M → R ⊗[F] E) → ℂ := A.indicator fun _ => 1 with hφ
  have hAclopen : IsClopen A := ⟨hAc.isClosed, hAo⟩
  have hφc : Continuous φ :=
    continuous_indicator (by simp [hAclopen.frontier_eq]) continuousOn_const
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _
  obtain ⟨⟨hg, -⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.GramDensity.isContDensityOn_gram F E σ h M J hJ R hloc 1 _ _ m hμ hν hfib φ hφc hφs
  have hfin : ∀ S, m S A < ⊤ := fun S => by
    haveI := (_root_.GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin F E σ h M J hJ R hloc 1 _ _ m hμ hν hfib S).1
    exact hAc.measure_lt_top
  have hint : ∀ S, ∫ X, φ X ∂(m S) = (((m S A).toReal : ℝ) : ℂ) := fun S => by
    rw [hφ, integral_indicator_const _ hAm]
    simp [Measure.real]
  have hcs : Continuous (hermScal R σ (F := F) (E := E)) := continuous_hermScal R

  have hqc : Continuous fun X : Fin 1 → Fin M → R ⊗[F] E =>
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) :=
    continuous_const.mul (htr.comp ((hgr 1 M J).matrix_elem 0 0))
  set K : Set R := (fun X : Fin 1 → Fin M → R ⊗[F] E =>
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0)) '' A with hKdef
  have hKc : IsCompact K := hAc.image hqc
  haveI : Nontrivial (R ⊗[F] E) := ⟨1, 0, fun e => by
    have h3 := GlobalTheory.CompanionTheory.SW.FibreRatio.half_trace_tmul (F := F) (E := E) R h (1 : R)
    rw [← Algebra.TensorProduct.one_def, e, map_zero, mul_zero] at h3
    exact zero_ne_one h3⟩
  have hK0 : (0 : R) ∉ K := by
    rintro ⟨X, hX, h0⟩
    have hu : IsUnit (gramR R σ J X).det := hAU hX
    rw [Matrix.det_fin_one, gram_entry R h hJ X] at hu
    simp only at h0
    rw [h0, TensorProduct.zero_tmul] at hu
    exact not_isUnit_zero hu
  have hzero : ∀ s, s ∉ K → m (hermScal R σ s) A = 0 := by
    intro s hs
    refine measure_mono_null ?_ (hfib.1 (hermScal R σ s))
    intro X hX hXG
    apply hs
    refine ⟨X, hX, ?_⟩
    have e : gramR R σ J X = (hermScal R σ s : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := hXG.1
    show algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) = s
    rw [e]
    exact qS_hermScal R h s
  have hcont : Continuous (fun s : R => (m (hermScal R σ s) A).toReal) := by
    rw [continuous_iff_continuousAt]
    intro s
    by_cases hs : s = 0
    · subst hs
      have hev : (fun _ : R => (0 : ℝ)) =ᶠ[𝓝 0] fun t : R => (m (hermScal R σ t) A).toReal := by
        filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hK0] with t ht
        simp [hzero t ht]
      exact continuousAt_const.congr hev
    · have hunit : hermScal R σ s ∈
          {S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} := by
        show IsUnit (Matrix.det _)
        rw [Matrix.det_fin_one]
        exact isUnit_tmul R hs
      have hne : ∀ᶠ t in 𝓝 s, t ≠ 0 := isOpen_ne.mem_nhds hs
      have htend : Filter.Tendsto (hermScal R σ) (𝓝 s)
          (𝓝[{S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det}]
            (hermScal R σ s)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨hcs.tendsto s, hne.mono fun t ht => ?_⟩
        show IsUnit (Matrix.det _)
        rw [Matrix.det_fin_one]
        exact isUnit_tmul R ht
      have := (Complex.continuous_re.tendsto _).comp ((hg _ hunit).tendsto.comp htend)
      simpa [ContinuousAt, Function.comp_def, hint] using this
  have hsupp : HasCompactSupport (fun s : R => (m (hermScal R σ s) A).toReal) :=
    HasCompactSupport.intro hKc fun s hs => by simp [hzero s hs]
  refine ⟨hcont, hsupp, ?_⟩
  have hνeq : coordHerm R σ b lam 1 = Measure.map (hermScal R σ) lam := by
    ext T hT
    rw [Measure.map_apply hcs.measurable hT,
      ← coordHerm_qS R h htr b lam (hcs.measurable hT : MeasurableSet (hermScal R σ ⁻¹' T))]
    congr 1
    ext S
    simp [hermScal_qS R h S]
  have hgS : ∀ S, m S A = ENNReal.ofReal ((m (hermScal R σ (qS R σ S)) A).toReal) := fun S => by
    rw [hermScal_qS R h S, ENNReal.ofReal_toReal (hfin S).ne]
  have hgm : Measurable fun S : HermR R σ 1 => m S A := by
    have e : (fun S : HermR R σ 1 => m S A) =
        fun S => ENNReal.ofReal ((m (hermScal R σ (qS R σ S)) A).toReal) := funext hgS
    rw [e]
    exact ENNReal.measurable_ofReal.comp (hcont.comp (continuous_qS R htr)).measurable
  have hV : MeasurableSet ({0}ᶜ : Set R) := (measurableSet_singleton 0).compl
  have hP : MeasurableSet {S : HermR R σ 1 | qS R σ S ∈ ({0}ᶜ : Set R)} :=
    (continuous_qS R htr).measurable hV
  have hQ : MeasurableSet {X : Fin 1 → Fin M → R ⊗[F] E |
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ ({0}ᶜ : Set R)} :=
    hqc.measurable hV
  have heq := mass_eq_lintegral R h hJ hfib hAm (V := {0}ᶜ) (by simp) hQ hP
  have hAQ : A ∩ {X : Fin 1 → Fin M → R ⊗[F] E |
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ ({0}ᶜ : Set R)} = A := by
    refine Set.inter_eq_left.mpr fun X hX e => hK0 ⟨X, hX, e⟩
  rw [hAQ, ← lintegral_indicator hP] at heq
  have hind : {S : HermR R σ 1 | qS R σ S ∈ ({0}ᶜ : Set R)}.indicator (fun S => m S A) =
      fun S => m S A := by
    funext S
    by_cases hS : S ∈ {S : HermR R σ 1 | qS R σ S ∈ ({0}ᶜ : Set R)}
    · exact Set.indicator_of_mem hS _
    · rw [Set.indicator_of_notMem hS]
      have h0 : qS R σ S = 0 := by simpa using hS
      have e : S = hermScal R σ 0 := by rw [← h0, hermScal_qS R h S]
      rw [e, hzero 0 hK0]
  rw [hind, hνeq, lintegral_map hgm hcs.measurable] at heq
  rw [ofReal_integral_eq_lintegral_ofReal (hcont.integrable_of_hasCompactSupport hsupp)
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg), heq]
  exact lintegral_congr fun s => ENNReal.ofReal_toReal (hfin _).ne

theorem fibre_masses : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
  (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)),
  IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m →
  ∀ A : Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E), IsCompact A → IsOpen A → A ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det} →
  Continuous (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  HasCompactSupport (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  ENNReal.ofReal (∫ s, (m (hermScal (Fv F v) σ s) A).toReal ∂lam) = coordW (Fv F v) b lam 1 2 A := by
  intro F E _ _ _ _ _ σ hσ J hJ d b v lam hlam m hfib A hAc hAo hAU
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  exact masses_field (Fv F v) (_root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) hσ hJ b lam hlam.1 m hfib A hAc hAo hAU

end GlobalTheory.CompanionTheory.SW.FibreCpt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderQuadraticAlmostAll
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SW.QuadRing

open GlobalTheory.CompanionTheory.SW.GoodRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem quad_at {d : ℕ} (b : Module.Basis (Fin d) F E)
    (b₂ : Module.Basis (Fin 2) F E) (D : F) (hb0 : b₂ 0 = 1)
    (hD : b₂ 1 * b₂ 1 = algebraMap F E D) (v : HeightOneSpectrum (𝓞 F))
    (hD1 : Valued.v (algebraMap F (Fv F v) D) = 1)
    (h21 : Valued.v (algebraMap F (Fv F v) 2) = 1)
    (hBC : ∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈
      v.adicCompletionIntegers F)
    (hCB : ∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈
      v.adicCompletionIntegers F)
    (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) :
    ∃ (ι : v.adicCompletionIntegers F →+* O) (δ : O) (D : v.adicCompletionIntegers F),
      (δ * δ = ι D) ∧ (∀ y : O, ∃ p q : v.adicCompletionIntegers F, y = ι p + ι q * δ) ∧
      (∀ p q : v.adicCompletionIntegers F, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) ∧
      IsUnit D ∧ IsUnit (2 : v.adicCompletionIntegers F) := by
  set K := Fv F v with hK
  set B := Algebra.TensorProduct.basis K b₂ with hB
  set C := Algebra.TensorProduct.basis K b with hC
  let Rs : Subring K := (v.adicCompletionIntegers F).toSubring
  have hB0 : B 0 = 1 := by
    rw [hB, Algebra.TensorProduct.basis_apply, hb0]; rfl
  have hB1 : B 1 = inclR K (b₂ 1) := by
    rw [hB, Algebra.TensorProduct.basis_apply]; rfl
  have hBD : B 1 * B 1 = algebraMap K (K ⊗[F] E) (algebraMap F K D) := by
    rw [hB1, ← map_mul, hD]
    show (1 : Fv F v) ⊗ₜ[F] algebraMap F E D = (algebraMap F (Fv F v) D) ⊗ₜ[F] (1 : E)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  have hDR : algebraMap F K D ∈ Rs := hD1.le
  have hBC' : ∀ k j, B.repr (C k) j ∈ Rs := fun k j => by
    have := hBC k j
    rwa [show inclR K (b k) = C k by rw [hC, Algebra.TensorProduct.basis_apply]; rfl] at this
  have hCB' : ∀ j k, C.repr (B j) k ∈ Rs := fun j k => by
    have := hCB j k
    rwa [show inclR K (b₂ j) = B j by rw [hB, Algebra.TensorProduct.basis_apply]; rfl] at this
  have hOB : ∀ y, y ∈ O ↔ ∀ j, B.repr y j ∈ Rs := fun y =>
    ⟨fun hy j => coord_mem Rs C B hBC' y ((hO y).1 hy) j,
      fun hy => (hO y).2 fun k => coord_mem Rs B C hCB' y hy k⟩
  have hpq : ∀ p q : K, p ∈ Rs → q ∈ Rs →
      algebraMap K (K ⊗[F] E) p + algebraMap K (K ⊗[F] E) q * B 1 ∈ O := by
    intro p q hp hq
    have h := coord_two B hB0 p q
    refine (hOB _).2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · rw [h.1]; exact hp
    · rw [h.2]; exact hq
  have hRmem : ∀ c ∈ Rs, algebraMap K (K ⊗[F] E) c ∈ O := by
    intro c hc
    simpa using hpq c 0 hc Rs.zero_mem
  have hδO : B 1 ∈ O := by
    have := hpq 0 1 Rs.zero_mem Rs.one_mem
    rwa [map_zero, map_one, zero_add, one_mul] at this
  let ι : (v.adicCompletionIntegers F) →+* O :=
    ((algebraMap K (K ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype).codRestrict O
      (fun x => hRmem x x.2)
  let δ : O := ⟨B 1, hδO⟩
  let D' : v.adicCompletionIntegers F := ⟨algebraMap F K D, hDR⟩
  have hδ : δ * δ = ι D' := Subtype.ext hBD
  have hsp : ∀ y : O, ∃ p q : v.adicCompletionIntegers F, y = ι p + ι q * δ := fun y => by
    have hy := (hOB y).1 y.2
    exact ⟨⟨_, hy 0⟩, ⟨_, hy 1⟩, Subtype.ext (eq_coord B hB0 y)⟩
  have hinj : ∀ p q : v.adicCompletionIntegers F, ι p + ι q * δ = 0 → p = 0 ∧ q = 0 := by
    intro p q h
    have h' : algebraMap K (K ⊗[F] E) (p : K) + algebraMap K (K ⊗[F] E) (q : K) * B 1 = 0 :=
      congrArg Subtype.val h
    have hc := coord_two B hB0 (p : K) (q : K)
    rw [h'] at hc
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply] at hc
    exact ⟨Subtype.ext hc.1.symm, Subtype.ext hc.2.symm⟩
  have hunit : ∀ r : v.adicCompletionIntegers F, IsUnit r ↔ Valued.v (r : K) = 1 := fun r =>
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
  have hv2 : Valued.v (2 : K) = 1 := by simpa [map_ofNat] using h21
  have hDu : IsUnit D' := (hunit D').2 hD1
  have h2u : IsUnit (2 : v.adicCompletionIntegers F) := (hunit 2).2 (by
    rw [show ((2 : v.adicCompletionIntegers F) : K) = 2 from
      map_ofNat (v.adicCompletionIntegers F).subtype 2]
    exact hv2)
  exact ⟨ι, δ, D', hδ, hsp, hinj, hDu, h2u⟩

theorem quad_ring : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∃ (ι : v.adicCompletionIntegers F →+* O) (δ : O) (D : v.adicCompletionIntegers F), (δ * δ = ι D) ∧ (∀ y : O, ∃ p q : v.adicCompletionIntegers F, y = ι p + ι q * δ) ∧ (∀ p q : v.adicCompletionIntegers F, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) ∧ IsUnit D ∧ IsUnit (2 : v.adicCompletionIntegers F) := by
  intro F E _ _ _ _ _ σ h d b
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hc
    push_neg at hc
    obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
    have hreal : w.IsReal := by
      rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.isReal_mk_iff,
        NumberField.ComplexEmbedding.isReal_iff]
      refine RingHom.ext fun x ↦ ?_
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      change star (w.embedding x) = w.embedding x
      rw [← h.2.2.2, hc]
    exact NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w) hreal
  obtain ⟨D, b₂, hsq, hb0, hσ1, hD⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ h.2.2.1 hinv hne
  have hD0 : D ≠ 0 := fun h0 => hsq (h0 ▸ IsSquare.zero)
  have I := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ h
  filter_upwards [(I d b).2 D hD0, (I d b).2 2 two_ne_zero,
    Filter.eventually_all.2 fun k => (I 2 b₂).1 (b k),
    Filter.eventually_all.2 fun j => (I d b).1 (b₂ j)] with v hD1 h21 hBC hCB O hO
  exact quad_at b b₂ D hb0 hD v hD1 h21 hBC hCB O hO

end GlobalTheory.CompanionTheory.SW.QuadRing
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemFixedIffIdempotentSum
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.FixW

section Idem

variable {R I J : Type} [CommRing R] [Fintype I] [Fintype J]

end Idem

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

end GlobalTheory.CompanionTheory.FixW
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpSurjectiveKerSpan
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem sharp_map_surjective_ker {l : ℕ} [Fact l.Prime] (A : PAlg l) :
    Function.Surjective A.aToU1 ∧ RingHom.ker A.aToU1 = Ideal.span {A.pi} := by
  constructor
  · intro y
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
    exact ⟨x.coeff 0, A.sharpMap_coeff x⟩
  · ext a
    rw [RingHom.mem_ker]
    constructor
    · intro h
      rw [A.sharpMap_eq, Ideal.Quotient.eq_zero_iff_mem, pow_one] at h
      obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 h
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective u
      have h0 : A.th (WittVector.teichmuller l a - y * (l : A.W)) = 0 := by
        rw [map_sub, map_mul, map_natCast]
        exact sub_eq_zero.2 hu.symm
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
      have h1 := congrArg (WittVector.constantCoeff : A.W →+* A.A) hc
      rw [map_mul, map_sub, map_mul, map_natCast, A.natCast_l, mul_zero, sub_zero,
        WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
        WittVector.teichmuller_coeff_zero, A.xi_coeff_zero] at h1
      exact Ideal.mem_span_singleton'.2 ⟨-c.coeff 0, by rw [← h1, neg_mul, mul_neg]⟩
    · intro h
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
      rw [map_mul, A.sharpMap_eq A.pi, A.sharp_pi,
        Ideal.Quotient.eq_zero_iff_mem.2 (by
          rw [pow_one]; exact Ideal.mem_span_singleton_self _), mul_zero]

end GlobalTheory.CompanionTheory.Untilt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoOfAsymptoticBoundsStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_of_asymptotic_bounds : ∀ (f : ℕ → ℝ) (G : ℝ) (D : ℕ), (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (G - ε) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤ f n) → (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, f n ≤ (G + ε) * (n : ℝ) ^ D / (D.factorial : ℝ)) → Tendsto (fun n : ℕ => (D.factorial : ℝ) * f n / (n : ℝ) ^ D) atTop (𝓝 G) := by
  first | exact @GlobalTheory.CompanionTheory.Analysis.tendsto_factorial_mul_div_pow_of_eps_bounds | exact GlobalTheory.CompanionTheory.Analysis.tendsto_factorial_mul_div_pow_of_eps_bounds | (intros; apply GlobalTheory.CompanionTheory.Analysis.tendsto_factorial_mul_div_pow_of_eps_bounds <;> assumption)
end

