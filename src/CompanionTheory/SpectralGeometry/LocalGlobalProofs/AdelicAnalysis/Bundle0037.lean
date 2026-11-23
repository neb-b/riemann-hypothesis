module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0029
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0036
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulA
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0031
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductUnfold
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0034
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0035
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0030

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsGramFiberMeasures
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramExist

theorem exists_gramFib : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ m, IsGramFib R σ J n μ ν m := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n μ ν hμ hν
  have hR' := hR
  obtain ⟨htr, hlc, hsc, ht2, -, -, -, -⟩ := hR'
  obtain ⟨hKtr, hKlc, hKsc, hKt2, -, -, -, hKb, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  have hKu := _root_.GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hCM R hR
  obtain ⟨hXlc, hXsc, hXt2, hXb, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM R n
  obtain ⟨g, hg, hgf⟩ := hlift M J hJ
  haveI := hKb n M
  have hinj : Function.Injective (Subtype.val : HermR R σ n → Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    Subtype.val_injective
  have hBo : IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    have hc : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have : {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} =
        (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
          Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_range]
      rfl
    rw [this]
    exact hKu.isOpen_range.preimage hc
  have hpre : ∀ B' : Set (HermR R σ n), gramR R σ J ⁻¹' (Subtype.val '' B') = g ⁻¹' B' := by
    intro B'
    ext X
    simp only [Set.mem_preimage, Set.mem_image, hgf X]
    exact hinj.mem_set_image
  have hglue := GlobalTheory.CompanionTheory.SW.FibreGlue.glue (Fin n → Fin M → R ⊗[F] E) (HermR R σ n)
    (Matrix (Fin n) (Fin n) (R ⊗[F] E)) μ ν (gramR R σ J) g Subtype.val hinj hg hgf
    {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} hBo ?_
  · obtain ⟨fib, hfib⟩ := hglue
    refine ⟨fib, ?_⟩
    have hU : {X | IsUnit (gramR R σ J X).det} =
        g ⁻¹' {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hgf X]
    unfold IsGramFib
    rw [hU]
    exact hfib
  · intro S hS
    obtain ⟨B, hB, hSB, hBu, fib, hfib⟩ :=
      _root_.GlobalTheory.CompanionTheory.SW.GramNear.exists_fibre_near F E σ hCM M J hJ R hR n μ ν hμ hν S hS
    refine ⟨B, hB, hSB, fun S' hS' => hBu S' hS', fib, ?_⟩
    rw [← hpre]
    exact hfib

end GlobalTheory.CompanionTheory.SW.GramExist
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ProdFormula

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise

section Infinite

variable {F : Type} [Field F] [NumberField F]

theorem map_mul_left_infinite {m : MeasurableSpace (InfiniteAdeleRing F)}
    (hm : @BorelSpace _ _ m) (b : (InfiniteAdeleRing F)ˣ) (μ : Measure (InfiniteAdeleRing F))
    (hμ : μ.IsAddHaarMeasure) :
    μ.map (fun y => (b : InfiniteAdeleRing F) * y) =
      ENNReal.ofReal ‖((b⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)‖ • μ := by
  obtain rfl : m = GroundTheory.Global.measurableSpace_infiniteAdeleRing F :=
    hm.measurable_eq.trans (GroundTheory.Global.borelSpace_infiniteAdeleRing (K := F)).measurable_eq.symm
  have h := Measure.isAddLeftInvariant_eq_smul μ (GroundTheory.Global.infiniteAdeleMeasure F)
  rw [h, Measure.map_smul, GroundTheory.Global.map_mul_left_infiniteAdeleMeasure, smul_comm]
  exact (continuous_const_mul (b : InfiniteAdeleRing F)).measurable.aemeasurable

theorem norm_algebraMap_infinite (a : F) :
    ‖algebraMap F (InfiniteAdeleRing F) a‖ = ∏ w : InfinitePlace F, w a ^ w.mult := by
  rw [InfiniteAdeleRing.norm_def]
  refine Finset.prod_congr rfl fun w _ => ?_
  congr 1
  rw [InfiniteAdeleRing.algebraMap_apply]
  exact AbsoluteValue.Completion.norm_coe (WithAbs.toAbs w.1 a)

end Infinite

section Finite

open HeckeCharacterZeroLocus.SiegelWeilU

variable {F : Type} [Field F] [NumberField F]

theorem distribHaarChar_eq_nnnorm (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (ha : a ≠ 0) :
    distribHaarChar (Fv F v) (Units.mk0 a ha) = ‖a‖₊ := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  let ϖ : Fv F v := (π : Fv F v)
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hva : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  set k : ℤ := WithZero.log (Valued.v a) with hk
  have hu0 : a * ϖ ^ k ≠ 0 := mul_ne_zero ha (zpow_ne_zero _ hϖ0)
  have hu : Valued.v (a * ϖ ^ k) = 1 := by
    rw [map_mul, map_zpow₀, hϖ, ← WithZero.exp_log hva, ← WithZero.exp_zsmul, ← WithZero.exp_add,
      ← hk, ← WithZero.exp_zero]
    congr 1
    simp
  have hU : Units.mk0 (a * ϖ ^ k) hu0 = Units.mk0 a ha * (Units.mk0 ϖ hϖ0) ^ k := by
    ext; simp [Units.val_zpow_eq_zpow_val]
  have h1 := PI.UnitaryGroupMassFormula.LocJacTyp.BM.dhc_unit v _ hu hu0
  rw [hU, map_mul, map_zpow, PI.UnitaryGroupMassFormula.LocJacTyp.BM.dhc_unif v ϖ hϖ hϖ0, inv_zpow] at h1
  have hq : ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ k ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast PI.UnitaryGroupMassFormula.LocJacTyp.BM.q_ne_zero v)
  have h2 : distribHaarChar (Fv F v) (Units.mk0 a ha) = ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ k :=
    (mul_inv_eq_one₀ hq).1 h1
  rw [h2]
  apply NNReal.coe_injective
  rw [coe_nnnorm, ← GroundTheory.Global.normalizedAbv_apply, GroundTheory.Global.normalizedAbv_eq_zpow v ha, ← hk]
  simp

theorem map_mul_left_finite (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (ha : a ≠ 0)
    (μ : Measure (Fv F v)) (hμ : μ.IsAddHaarMeasure) :
    μ.map (fun x => a * x) = (‖a‖₊)⁻¹ • μ := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  haveI : μ.Regular := inferInstance
  ext S hS
  rw [Measure.map_apply (continuous_const_mul _).measurable hS, Measure.smul_apply]
  have h := distribHaarChar_mul μ (Units.mk0 a ha)⁻¹ S
  have e : (fun x => a * x) ⁻¹' S = (Units.mk0 a ha)⁻¹ • S :=
    Set.preimage_smul (Units.mk0 a ha) S
  rw [e, ← h, map_inv, distribHaarChar_eq_nnnorm]
  rfl

end Finite

section Main

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW

theorem unitProd_scalar : ∀ (F : Type) [Field F] [NumberField F] (a : F), a ≠ 0 →
    ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧
      (∀ μ : Measure (Ainf F), μ.IsAddHaarMeasure →
        μ.map (fun x => algebraMap F (Ainf F) a * x) = cinf • μ) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ∀ μ : Measure (Fv F v), μ.IsAddHaarMeasure →
        μ.map (fun x => algebraMap F (Fv F v) a * x) = c v • μ := by
  intro F _ _ a ha
  have hA : 0 < ∏ w : InfinitePlace F, w a ^ w.mult :=
    Finset.prod_pos fun w _ => pow_pos (InfinitePlace.pos_iff.2 ha) _
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖algebraMap F (Fv F v) a‖).Finite :=
    (FinitePlace.hasFiniteMulSupport ha).preimage
      (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn
  have hprod : (∏ w : InfinitePlace F, w a ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (Fv F v) a‖ = 1 := by
    rw [← prod_abs_eq_one ha, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    rfl
  refine ⟨((∏ w : InfinitePlace F, w a ^ w.mult)⁻¹).toNNReal,
    fun v => (‖algebraMap F (Fv F v) a‖₊)⁻¹, ⟨?_, ?_⟩, ?_, ?_⟩
  · filter_upwards [hfin.eventually_cofinite_notMem] with v hv
    have h1 : ‖algebraMap F (Fv F v) a‖ = 1 := by simpa using hv
    have h2 : ‖algebraMap F (Fv F v) a‖₊ = 1 := NNReal.coe_injective h1
    rw [h2, inv_one]
  · apply NNReal.coe_injective
    have e : ((∏ᶠ v : HeightOneSpectrum (𝓞 F), (‖algebraMap F (Fv F v) a‖₊)⁻¹ : ℝ≥0) : ℝ) =
        (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (Fv F v) a‖)⁻¹ := by
      rw [finprod_inv_distrib]
      rw [NNReal.coe_inv]
      congr 1
      exact NNReal.toRealHom.map_finprod_of_injective NNReal.coe_injective _
    rw [NNReal.coe_mul, e, NNReal.coe_one, Real.coe_toNNReal _ (inv_pos.2 hA).le, ← mul_inv, hprod, inv_one]
  · intro μ hμ
    have hb : (((Units.map (algebraMap F (Ainf F)).toMonoidHom (Units.mk0 a ha))⁻¹ : (Ainf F)ˣ) : Ainf F) =
        algebraMap F (Ainf F) a⁻¹ := by
      simp
    have h := map_mul_left_infinite (F := F) (m := measAinf) ⟨rfl⟩
      (Units.map (algebraMap F (Ainf F)).toMonoidHom (Units.mk0 a ha)) μ hμ
    rw [hb, norm_algebraMap_infinite] at h
    have e : ∏ w : InfinitePlace F, w a⁻¹ ^ w.mult = (∏ w : InfinitePlace F, w a ^ w.mult)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun w _ => by rw [map_inv₀, inv_pow]
    rw [e] at h
    exact h
  · intro v μ hμ
    exact map_mul_left_finite v _ ((map_ne_zero _).2 ha) μ hμ

end Main

end GlobalTheory.CompanionTheory.SW.ProdFormula
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductDensity
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold

theorem measurable_vec {K : Type} [Zero K] [MeasurableSpace K] {M n : ℕ} (α : K) :
    Measurable (fun p : (Fin n → K) × (Fin n → Fin M → K) => vec α p.1 p.2) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp only [vec, Fin.cons_zero]
    exact measurable_const
  · refine Fin.cases ?_ (fun j' => ?_) j
    · simp only [vec, Fin.cons_succ, Fin.cons_zero]
      exact (measurable_pi_apply i').comp measurable_fst
    · simp only [vec, Fin.cons_succ]
      exact (measurable_pi_apply j').comp ((measurable_pi_apply i').comp measurable_snd)

theorem swap_through_fibres {Y C X H : Type} [MeasurableSpace Y] [MeasurableSpace C] [MeasurableSpace X]
    [MeasurableSpace H] (μ₁ : Measure Y) (μc : Measure C) (μ : Measure X) (ν : Measure H)
    [SFinite μ₁] [SFinite μc] [SFinite μ] (U : Set X) (W : Set H) (hW : MeasurableSet W)
    (m : H → Measure X) (hm : ∀ S, SFinite (m S)) (hoff : ∀ S, S ∉ W → m S = 0)
    (hfib : ∀ ψ : X → ℝ≥0∞, Measurable ψ → ∫⁻ v in U, ψ v ∂μ = ∫⁻ S, ∫⁻ v, ψ v ∂(m S) ∂ν)
    (f : Y → C → X → ℝ≥0∞) (hf : Measurable fun p : Y × C × X => f p.1 p.2.1 p.2.2) :
    ∫⁻ y, ∫⁻ c, ∫⁻ S in W, ∫⁻ v, f y c v ∂(m S) ∂ν ∂μc ∂μ₁ =
      ∫⁻ c, ∫⁻ S in W, ∫⁻ y, ∫⁻ v, f y c v ∂(m S) ∂μ₁ ∂ν ∂μc := by
  have restr : ∀ G : H → ℝ≥0∞, (∀ S, S ∉ W → G S = 0) → ∫⁻ S in W, G S ∂ν = ∫⁻ S, G S ∂ν := by
    intro G hG
    rw [← lintegral_indicator hW]
    refine lintegral_congr fun S => ?_
    by_cases hS : S ∈ W
    · simp [hS]
    · simp [hS, hG S hS]
  have hfyc : ∀ y c, Measurable (f y c) := fun y c =>
    hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hfc : ∀ c, Measurable fun p : Y × X => f p.1 c p.2 := fun c =>
    hf.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have e1 : ∀ y c, ∫⁻ S in W, ∫⁻ v, f y c v ∂(m S) ∂ν = ∫⁻ v in U, f y c v ∂μ := by
    intro y c
    rw [hfib _ (hfyc y c)]
    refine restr _ fun S hS => ?_
    simp [hoff S hS]
  have hyc : Measurable fun q : Y × C => ∫⁻ v in U, f q.1 q.2 v ∂μ := by
    have : Measurable fun r : (Y × C) × X => f r.1.1 r.1.2 r.2 :=
      hf.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact this.lintegral_prod_right'
  calc ∫⁻ y, ∫⁻ c, ∫⁻ S in W, ∫⁻ v, f y c v ∂(m S) ∂ν ∂μc ∂μ₁
      = ∫⁻ y, ∫⁻ c, ∫⁻ v in U, f y c v ∂μ ∂μc ∂μ₁ := by simp only [e1]
    _ = ∫⁻ c, ∫⁻ y, ∫⁻ v in U, f y c v ∂μ ∂μ₁ ∂μc :=
        lintegral_lintegral_swap (f := fun y c => ∫⁻ v in U, f y c v ∂μ) hyc.aemeasurable
    _ = ∫⁻ c, ∫⁻ v in U, ∫⁻ y, f y c v ∂μ₁ ∂μ ∂μc := by
        refine lintegral_congr fun c => ?_
        exact lintegral_lintegral_swap (f := fun y v => f y c v) (hfc c).aemeasurable
    _ = ∫⁻ c, ∫⁻ S in W, ∫⁻ y, ∫⁻ v, f y c v ∂(m S) ∂μ₁ ∂ν ∂μc := by
        refine lintegral_congr fun c => ?_
        rw [hfib _ (hfc c).lintegral_prod_left']
        rw [restr]
        · refine lintegral_congr fun S => ?_
          haveI := hm S
          exact lintegral_lintegral_swap (f := fun v y => f y c v)
            ((hfc c).comp measurable_swap).aemeasurable
        · intro S hS
          simp [hoff S hS]

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem lintegral_Uset_eq_Mid : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = Mid σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hCM := D.hCM
  have hlam := D.hlam
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id D.hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  obtain ⟨hK, hW, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam hlam
  have hJ' := GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  obtain ⟨-, hlf1, -, -, -, hae1⟩ := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ hCM (M + 1) 1 _ hJ' R D.hR d b lam hlam m₁ D.hm₁
  obtain ⟨hUo, hlf, hoff, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ hCM M n J D.hJ R D.hR d b lam hlam m' D.hm'
  obtain ⟨-, -, h₃, -, h₅, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hCM (M + 1) _ hJ' R
  have hc := (hact (n + 1)).1
  haveI := hBorel n M
  haveI := hBorel (n + 1) (M + 1)
  haveI := hBorel 1 (M + 1)
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  haveI : SigmaFinite (coordW R b lam n M) := inferInstance
  haveI : SigmaFinite (m₁ (hermScal R σ (algebraMap F R t))) := inferInstance
  haveI : BorelSpace (HermR R σ n) := ⟨rfl⟩
  haveI : SFinite (Measure.pi fun _ : Fin n => coordK R b lam) := inferInstance
  have hm : ∀ S, SFinite (m' S) := fun S => inferInstance
  have hUm : MeasurableSet (Unt σ R n) := hUo.measurableSet
  have hB : MeasurableSet B₀ := D.hB₀.measurableSet
  rw [_root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1.first_step F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ]
  unfold Mid
  refine setLIntegral_congr_fun hB fun x hx => ?_
  refine congrArg _ ?_
  set f : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → (Fin n → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E) → ℝ≥0∞ :=
    fun y₀ c X => φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) with hfdef
  have hf : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      f p.1 p.2.1 p.2.2 := by
    have hcm : Measurable (fun p : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) p.1 p.2) := by
      haveI : SecondCountableTopology (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := inferInstance
      haveI : OpensMeasurableSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := inferInstance
      haveI : OpensMeasurableSpace (HA R σ (blockOne (algebraMap F E t) J)) := inferInstance
      haveI : OpensMeasurableSpace (HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) :=
        Prod.opensMeasurableSpace
      exact hc.measurable
    have hg : Measurable (fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        ((s p.1, vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) p.2.1 p.2.2) :
          HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E))) :=
      (D.hs.comp measurable_fst).prodMk
        ((Unfold.measurable_vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E))).comp measurable_snd)
    exact hφ.comp (hcm.comp hg)
  have hae : ∀ᵐ y₀ ∂(m₁ (hermScal R σ (algebraMap F R t))),
      chi σ J t s a b lam ((Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ)
          (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) =
        ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S' in Unt σ R n, ∫⁻ X, f y₀ c X ∂(m' S') ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by
    filter_upwards [hae1 (hermScal R σ (algebraMap F R t))] with y₀ hy₀
    exact _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.chi_at_fibre F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ x hx y₀ hy₀
  rw [lintegral_congr_ae hae]
  exact Unfold.swap_through_fibres (m₁ (hermScal R σ (algebraMap F R t)))
    (Measure.pi fun _ => coordK R b lam) (coordW R b lam n M) (coordHerm R σ b lam n)
    {X | IsUnit (gramR R σ J X).det} (Unt σ R n) hUm m' hm hoff D.hm'.2.1 f hf

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductFubiniStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_Pint' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → Measurable (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Pint σ J t m₁ m' s φ z.1 z.2.1 z.2.2) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.measurable_Pint | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.measurable_Pint | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.measurable_Pint <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductRecursion
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_integrable_continuousOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → (∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), Integrable φ (fibS σ J t m₁ m' s B₀ a κ₁ cm S)) ∧ ContinuousOn (fun S => ∫ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S)) (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ hφc
  have h1 := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.integrable_fibS_and_integral F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ hφc
  have h2 := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo.cont_double F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ hφc
  obtain ⟨-, ha, hc, hsch, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord.coords F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  refine ⟨fun S hS => (h1 S hS).1, ?_⟩
  have hsub : (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) ⊆
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := fun S hS => hS.1
  have ha' := ha.mono hsub
  have hval := Units.continuous_val.comp_continuousOn ha'
  have hmap := hval.prodMk ((hc.mono hsub).prodMk (hsch.mono hsub))
  have hP := h2.comp hmap (fun S hS => ⟨(a _).isUnit, Set.mem_univ _, hS.2⟩)
  have hk := NNReal.continuous_coe.comp_continuousOn
    ((D.hκc.comp_continuousOn ha').mul ((D.hcmc.comp_continuousOn ha').pow n))
  exact (hk.mul hP).congr (fun S hS => (h1 S hS).2)
end

