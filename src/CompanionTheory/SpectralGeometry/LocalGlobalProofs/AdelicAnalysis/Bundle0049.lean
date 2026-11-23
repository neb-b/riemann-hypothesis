module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureScaling
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0007
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
public import GroundTheory.GlobalFields.LocalAtPlace
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0048
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacter

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureLinearChange
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.PiScale

section Abstract

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R]
  [BorelSpace R] [SecondCountableTopology R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem continuous_mulVec_left (M : Matrix ι ι R) : Continuous (fun x : ι → R => M *ᵥ x) :=
  Continuous.matrix_mulVec continuous_const continuous_id

theorem image_mulVec_eq_preimage (M N : Matrix ι ι R) (h1 : M * N = 1) (h2 : N * M = 1)
    (s : Set (ι → R)) : (fun x => M *ᵥ x) '' s = (fun x => N *ᵥ x) ⁻¹' s := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [Matrix.mulVec_mulVec, h2] using hx
  · intro hy
    exact ⟨N *ᵥ y, hy, by simp [Matrix.mulVec_mulVec, h1]⟩

theorem pi_image_mul (lf : Measure R) [SigmaFinite lf] (u v : ι → R) (huv : ∀ i, u i * v i = 1)
    (c : ι → ℝ≥0)
    (hc : ∀ i (s : Set R), MeasurableSet s → lf ((fun x => u i * x) '' s) = (c i : ℝ≥0∞) * lf s)
    (s : Set (ι → R)) (hs : MeasurableSet s) :
    (Measure.pi fun _ : ι => lf) ((fun x i => u i * x i) '' s) =
      (∏ i, (c i : ℝ≥0∞)) * (Measure.pi fun _ : ι => lf) s := by
  have hT : Measurable (fun (x : ι → R) i => v i * x i) :=
    (continuous_pi fun i => continuous_const.mul (continuous_apply i)).measurable
  have himg : (fun (x : ι → R) i => u i * x i) '' s = (fun (x : ι → R) i => v i * x i) ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : (fun i => v i * (u i * x i)) = x := by
        funext i
        rw [← mul_assoc, mul_comm (v i), huv, one_mul]
      simpa [this] using hx
    · intro hy
      refine ⟨_, hy, ?_⟩
      funext i
      show u i * (v i * y i) = y i
      rw [← mul_assoc, huv, one_mul]
  have hpre : ∀ i (t : Set R), (fun x => v i * x) ⁻¹' t = (fun x => u i * x) '' t := by
    intro i t
    ext y
    constructor
    · intro hy
      exact ⟨_, hy, by simp only; rw [← mul_assoc, huv, one_mul]⟩
    · rintro ⟨x, hx, rfl⟩
      have : v i * (u i * x) = x := by rw [← mul_assoc, mul_comm (v i), huv, one_mul]
      simpa [this] using hx
  have e1 : Measure.pi (fun i => c i • lf) =
      (Measure.pi fun _ : ι => lf).map (fun (x : ι → R) i => v i * x i) := by
    refine Measure.pi_eq fun t ht => ?_
    rw [Measure.map_apply hT (MeasurableSet.univ_pi ht)]
    have : (fun (x : ι → R) i => v i * x i) ⁻¹' Set.pi Set.univ t =
        Set.pi Set.univ fun i => (fun x => u i * x) '' t i := by
      ext x
      simp only [Set.mem_preimage, Set.mem_univ_pi, ← hpre]
    rw [this, Measure.pi_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hc i _ (ht i)]
    rfl
  have e2 : Measure.pi (fun i => c i • lf) =
      (∏ i, (c i : ℝ≥0∞)) • (Measure.pi fun _ : ι => lf) := by
    refine Measure.pi_eq fun t ht => ?_
    rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
    rfl
  rw [himg, ← Measure.map_apply hT hs, ← e1, e2, Measure.smul_apply, smul_eq_mul]

theorem measurePreserving_transvection (lf : Measure R) [SigmaFinite lf] [lf.IsAddLeftInvariant]
    (i j : ι) (hij : i ≠ j) (c : R) :
    MeasurePreserving (fun x : ι → R => transvection i j c *ᵥ x)
      (Measure.pi fun _ : ι => lf) (Measure.pi fun _ : ι => lf) := by
  have ht : Measurable (fun x : ι → R => transvection i j c *ᵥ x) :=
    (continuous_mulVec_left _).measurable
  refine ⟨ht, ?_⟩
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
  simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]
  refine lintegral_eq_of_lmarginal_eq {i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  have hup : ∀ xi : R, transvection i j c *ᵥ Function.update x i xi =
      Function.update x i (xi + c * x j) := by
    intro xi
    funext k
    by_cases hk : k = i
    · subst hk
      simp [transvection, add_mulVec, single_mulVec, hij.symm]
    · simp [transvection, add_mulVec, single_mulVec, hk, hij.symm]
  simp only [Function.comp_apply, hup]
  exact lintegral_add_right_eq_self
    (fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x i xᵢ)) (c * x j)

end Abstract

section Global

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem Bf_mul (g h : Matrix ι ι F) : Bf (g * h) = Bf g * Bf h := by
  simp [Bf, Matrix.map_mul]

theorem Bf_one : Bf (1 : Matrix ι ι F) = 1 := by
  simp [Bf]

theorem Bf_inv_mul (g : Matrix ι ι F) (hg : g.det ≠ 0) : Bf g⁻¹ * Bf g = 1 := by
  rw [← Bf_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg), Bf_one]

theorem Bf_mul_inv (g : Matrix ι ι F) (hg : g.det ≠ 0) : Bf g * Bf g⁻¹ = 1 := by
  rw [← Bf_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hg), Bf_one]

end Global

theorem pi_scale : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι], (∀ g : Matrix ι ι F, g.det ≠ 0 → ∀ s : Set (ι → A F), MeasurableSet s → (Measure.pi fun _ : ι => lf) ((fun x => Bf g *ᵥ x) '' s) = ENNReal.ofReal (|((Algebra.norm ℚ g.det : ℚ) : ℝ)|⁻¹) * (Measure.pi fun _ : ι => lf) s) ∧ ∀ (a : (A F)ˣ) (s : Set (ι → A F)), MeasurableSet s → (Measure.pi fun _ : ι => lf) ((fun x => (a : A F) • x) '' s) = lf ((fun x => (a : A F) * x) '' Oh F) ^ Fintype.card ι * (Measure.pi fun _ : ι => lf) s := by
  intro F _ _ _ _ lf hH h1 ι _ _
  obtain ⟨hlc, hsc, ht2, hOc, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F
  obtain ⟨hF, -, hU⟩ := _root_.GlobalTheory.CompanionTheory.SW.Core.Scale.lf_scale F lf hH h1
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI : SigmaFinite lf := inferInstance
  have hmeas : ∀ (g : Matrix ι ι F), g.det ≠ 0 → ∀ s : Set (ι → A F), MeasurableSet s →
      MeasurableSet ((fun x => Bf g *ᵥ x) '' s) := by
    intro g hg s hs
    rw [image_mulVec_eq_preimage _ _ (Bf_mul_inv g hg) (Bf_inv_mul g hg)]
    exact (continuous_mulVec_left _).measurable hs
  refine ⟨?_, ?_⟩
  · intro g hg
    refine diagonal_transvection_induction_of_det_ne_zero
      (fun g => ∀ s : Set (ι → A F), MeasurableSet s →
        (Measure.pi fun _ : ι => lf) ((fun x => Bf g *ᵥ x) '' s) =
          ENNReal.ofReal (|((Algebra.norm ℚ g.det : ℚ) : ℝ)|⁻¹) *
            (Measure.pi fun _ : ι => lf) s) g hg ?_ ?_ ?_
    · intro D hD s hs
      have hD' : ∀ i, D i ≠ 0 := by
        intro i
        rw [det_diagonal] at hD
        exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
      have hfun : (fun x : ι → A F => Bf (diagonal D) *ᵥ x) =
          fun x i => algebraMap F (A F) (D i) * x i := by
        funext x i
        have : Bf (diagonal D) = diagonal (fun i => algebraMap F (A F) (D i)) := by
          ext a b
          by_cases hab : a = b
          · subst hab; simp [Bf]
          · simp [Bf, hab]
        rw [this, mulVec_diagonal]
      rw [hfun, pi_image_mul lf (fun i => algebraMap F (A F) (D i))
        (fun i => algebraMap F (A F) (D i)⁻¹) ?_
        (fun i => Real.toNNReal (|((Algebra.norm ℚ (D i) : ℚ) : ℝ)|⁻¹)) ?_ s hs]
      · congr 1
        rw [det_diagonal, map_prod, Rat.cast_prod, Finset.abs_prod, ← Finset.prod_inv_distrib,
          ENNReal.ofReal_prod_of_nonneg fun i _ => inv_nonneg.2 (abs_nonneg _)]
        rfl
      · intro i
        rw [← map_mul, mul_inv_cancel₀ (hD' i), map_one]
      · intro i t ht
        exact hF (D i) (hD' i) t ht
    · intro t s hs
      have hdet : t.toMatrix.det = 1 := t.det
      have hinv : Bf t.toMatrix * Bf (transvection t.i t.j (-t.c)) = 1 := by
        rw [← Bf_mul, TransvectionStruct.toMatrix, transvection_mul_transvection_same _ _ t.hij]
        simp [Bf_one]
      have hinv' : Bf (transvection t.i t.j (-t.c)) * Bf t.toMatrix = 1 := by
        rw [← Bf_mul, TransvectionStruct.toMatrix, transvection_mul_transvection_same _ _ t.hij]
        simp [Bf_one]
      have hB : Bf (transvection t.i t.j (-t.c)) =
          transvection t.i t.j (algebraMap F (A F) (-t.c)) := by
        simp [Bf, transvection, Matrix.map_add (f := _), Matrix.map_one]
      rw [image_mulVec_eq_preimage _ _ hinv hinv', hB,
        (measurePreserving_transvection lf t.i t.j t.hij _).measure_preimage hs.nullMeasurableSet,
        hdet]
      simp
    · intro P Q hP hQ IP IQ s hs
      have himg : (fun x => Bf (P * Q) *ᵥ x) '' s =
          (fun x => Bf P *ᵥ x) '' ((fun x => Bf Q *ᵥ x) '' s) := by
        rw [Set.image_image]
        simp [Bf_mul, Matrix.mulVec_mulVec]
      rw [himg, IP _ (hmeas Q hQ s hs), IQ s hs, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 (abs_nonneg _)),
        det_mul, map_mul, Rat.cast_mul, abs_mul, mul_inv]
  · intro a s hs
    have hfin : lf ((fun x => (a : A F) * x) '' Oh F) ≠ ∞ :=
      (hOc.image (continuous_const.mul continuous_id)).measure_lt_top.ne
    have hfun : (fun x : ι → A F => (a : A F) • x) = fun x i => (a : A F) * x i := by
      funext x i
      rfl
    rw [hfun, pi_image_mul lf (fun _ => (a : A F)) (fun _ => ((a⁻¹ : (A F)ˣ) : A F)) (fun _ => by simp)
      (fun _ => (lf ((fun x => (a : A F) * x) '' Oh F)).toNNReal) ?_ s hs]
    · simp [ENNReal.coe_toNNReal hfin]
    · intro _ t ht
      rw [ENNReal.coe_toNNReal hfin]
      exact hU a t ht

end GlobalTheory.CompanionTheory.SW.Core.PiScale
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicLatticeMeasureFormula
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem muF_latN : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (N : ℕ), 0 < N → (muF B lf (latN F ι N : Set (ι → A F))).toReal = kap F ^ Fintype.card ι * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹ * (((N : ℝ) ^ Module.finrank ℚ F)⁻¹) ^ Fintype.card ι := by
  intro F _ _ _ _ lf hH h1 ι _ _ B N hN
  obtain ⟨hlc, hsc, ht2, -, hopen, -, -, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI : SigmaFinite lf := inferInstance
  have hscale := (_root_.GlobalTheory.CompanionTheory.SW.Core.Scale.lf_scale F lf hH h1).1
  have hNF : ((N : F)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hnorm : ((Algebra.norm ℚ (N : F) : ℚ) : ℝ) = (N : ℝ) ^ Module.finrank ℚ F := by
    have : (N : F) = algebraMap ℚ F (N : ℚ) := by simp
    rw [this, Algebra.norm_algebraMap]
    push_cast
    rfl
  set S : Set (A F) := (fun x => algebraMap F (A F) (N : F) * x) '' Oh F with hSdef
  have hlf : lf S = ENNReal.ofReal (((N : ℝ) ^ Module.finrank ℚ F)⁻¹) := by
    rw [hSdef, hscale (N : F) hNF (Oh F) hopen.measurableSet, h1, mul_one, hnorm,
      abs_of_nonneg (by positivity)]
  have hset : (latN F ι N : Set (ι → A F)) = Set.pi Set.univ (fun _ => S) := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_pi, Set.mem_univ, true_imp_iff, hSdef, Set.mem_image,
      map_natCast]
    constructor
    · intro h i
      obtain ⟨y, hy, e⟩ := h i
      exact ⟨y, hy, e.symm⟩
    · intro h i
      obtain ⟨y, hy, e⟩ := h i
      exact ⟨y, hy, e.symm⟩
  have hk : 0 ≤ kap F := inv_nonneg.mpr (Real.sqrt_nonneg _)
  rw [hset, muF, Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_const,
    Finset.card_univ, hlf, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal]
  positivity

end GlobalTheory.CompanionTheory.SW.ThW
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContDiffOnChartGlobalWhittakerCoefficient
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LatCpt

theorem latV_compact_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)), IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧ IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hCM d b n M v
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : T2Space (Fv F v) := inferInstance
  haveI : IsTopologicalRing (Fv F v) := inferInstance
  obtain ⟨-, -, -, -, -, -, hH, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)
  have hcoord := hH d b
  let H : (Fin n → Fin M → Fv F v ⊗[F] E) ≃ₜ (Fin n → Fin M → Fin d → Fv F v) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => hcoord.homeomorph
  let O : Set (Fv F v) := (v.adicCompletionIntegers F : Set (Fv F v))
  have hOc : IsCompact O := GroundTheory.Global.isCompact_adicCompletionIntegers v
  have hOo : IsOpen O := Valued.isOpen_valuationSubring _
  let P : Set (Fin n → Fin M → Fin d → Fv F v) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => O
  have hE : (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) = H ⁻¹' P := by
    ext Y
    simp only [latV, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi, P, O, SetLike.mem_coe]
    rfl
  have hPc : IsCompact P :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hOc
  have hPo : IsOpen P :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => hOo
  rw [hE]
  exact ⟨H.isCompact_preimage.2 hPc, hPo.preimage H.continuous⟩

end GlobalTheory.CompanionTheory.SW.LatCpt
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureTransport
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.EulerMove

theorem borel_ainf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → Ainf F ⊗[F] E) := by
  obtain ⟨⟨-, scA, -⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have scA' : SecondCountableTopology (Ainf F × Af F) := scA
  haveI : SecondCountableTopology (Ainf F) :=
    (isEmbedding_prodMkLeft (0 : Af F)).secondCountableTopology
  haveI : T2Space (Ainf F) := GlobalTheory.CompanionTheory.AdeleTop.t2Space_infiniteAdeleRing_of_numberField_field F
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)).2.2.2.2.2.2.2.1 n M

theorem borel_af (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → AF F ⊗[F] E) := by
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := lcA
  haveI := scA
  haveI := t2A
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)).2.2.2.2.2.2.2.1 n M

theorem borel_fv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : T2Space (Fv F v) := inferInstance
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)).2.2.2.2.2.2.2.1 n M

theorem euler_move : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf minf' : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m m' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (e : (Fin n → Fin M → AF F ⊗[F] E) → (Fin n → Fin M → AF F ⊗[F] E)) (einf : (Fin n → Fin M → Ainf F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E)) (ev : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable e → Measurable einf → (∀ v, Measurable (ev v)) → (∀ X, projInf (e X) = einf (projInf X) ∧ ∀ v, projV v (projFin (e X)) = ev v (projV v (projFin X))) → (∀ᶠ v in Filter.cofinite, ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v) → ∀ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c → minf.map einf = cinf • minf' → (∀ v, (m v).map (ev v) = c v • m' v) → (∀ v, m' v (latV b v) < ⊤) → IsEulerProd b I 1 minf m → IsEulerProd b (I.map e) 1 minf' m' := by
  intro F E _ _ _ _ _ σ hσ d b n M I minf minf' m m' e einf ev he heinf hev hcomm hgood cinf c hU
    hinf hloc hfin hE
  classical
  obtain ⟨-, hsum, S₀, hS₀⟩ := hE
  obtain ⟨hpi, hpf, hpv, hlat, hint, -⟩ := GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b n M
  haveI := borel_af F E σ hσ n M
  haveI := borel_ainf F E σ hσ n M
  haveI : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => borel_fv F E σ hσ n M v
  obtain ⟨S₁, hS₁⟩ := (GlobalTheory.CompanionTheory.SW.UnitProdAlg.main F cinf cinf c c hU hU).2.2.2.2.2.2.2
  let S₂ : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.1 hgood).toFinset
  have hS₂ : ∀ v, v ∉ S₂ → ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v := by
    intro v hv
    by_contra h
    exact hv (by simpa [S₂] using h)
  have hlatM : ∀ v, MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) :=
    fun v => (hlat v).2.measurableSet
  have hcv : ∀ v, v ∉ S₁ ∪ S₂ → c v = 1 := fun v hv =>
    ((hS₁ (S₁ ∪ S₂) Finset.subset_union_left).1 v hv)
  have hmm : ∀ v, v ∉ S₁ ∪ S₂ → m' v (latV b v) = m v (latV b v) := by
    intro v hv
    have hv₂ : v ∉ S₂ := fun h => hv (Finset.mem_union_right _ h)
    have h1 := congrArg (fun μ => μ (latV b v)) (hloc v)
    simp only [Measure.map_apply (hev v) (hlatM v), hcv v hv, one_smul] at h1
    rw [← h1]
    congr 1
    ext X
    exact hS₂ v hv₂ X
  refine ⟨hfin, ?_, S₀ ∪ (S₁ ∪ S₂), ?_⟩
  · refine hsum.congr_cofinite ?_
    have hfinite : (↑(S₁ ∪ S₂) : Set (HeightOneSpectrum (𝓞 F))).Finite := Finset.finite_toSet (S₁ ∪ S₂)
    filter_upwards [hfinite.compl_mem_cofinite] with v hv
    rw [hmm v (by simpa using hv)]
  · intro S hS φinf φ hφinf hφ
    have hSS₀ : S₀ ⊆ S := Finset.union_subset_left hS
    have hSS₃ : S₁ ∪ S₂ ⊆ S := Finset.union_subset_right hS
    have hSS₁ : S₁ ⊆ S := Finset.union_subset_left hSS₃
    have hnot : ∀ v, v ∉ S → v ∉ S₁ ∪ S₂ := fun v hv h => hv (hSS₃ h)
    have hpm : Measurable (pureL b S φinf φ) := by
      refine Measurable.indicator ?_ (hint S).measurableSet
      refine (hφinf.comp hpi.measurable).mul ?_
      refine Finset.measurable_prod _ fun v _ => ?_
      exact (hφ v).comp ((hpv v).comp hpf).measurable
    have hmem : ∀ X, e X ∈ intOff b S ↔ X ∈ intOff b S := by
      intro X
      refine forall_congr' fun v => ?_
      refine imp_congr_right fun hv => ?_
      rw [(hcomm X).2 v]
      exact hS₂ v (fun h => hnot v hv (Finset.mem_union_right _ h)) _
    have hfun : (fun X => pureL b S φinf φ (e X)) =
        pureL b S (fun Y => φinf (einf Y)) (fun v Y => φ v (ev v Y)) := by
      funext X
      unfold pureL
      by_cases hX : X ∈ intOff b S
      · rw [Set.indicator_of_mem ((hmem X).2 hX), Set.indicator_of_mem hX, (hcomm X).1]
        congr 1
        exact Finset.prod_congr rfl fun v _ => by rw [(hcomm X).2 v]
      · rw [Set.indicator_of_notMem (fun h => hX ((hmem X).1 h)), Set.indicator_of_notMem hX]
    have hinfI : ∫⁻ Y, φinf (einf Y) ∂minf = (cinf : ℝ≥0∞) * ∫⁻ Y, φinf Y ∂minf' := by
      rw [← lintegral_map hφinf heinf, hinf, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    have hvI : ∀ v, ∫⁻ Y, φ v (ev v Y) ∂(m v) = (c v : ℝ≥0∞) * ∫⁻ Y, φ v Y ∂(m' v) := by
      intro v
      rw [← lintegral_map (hφ v) (hev v), hloc v, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    have hone : (cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞) = 1 := by
      have := (hS₁ S hSS₁).2
      exact_mod_cast this
    have htail : (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) =
        ∏' v : {v // v ∉ S}, (m' v.1 (latV b v.1)).toReal :=
      tprod_congr fun v => by rw [hmm v.1 (hnot v.1 v.2)]
    rw [lintegral_map hpm he, hfun,
      hS₀ S hSS₀ (fun Y => φinf (einf Y)) (fun v Y => φ v (ev v Y)) (hφinf.comp heinf)
        (fun v => (hφ v).comp (hev v)), hinfI, htail]
    simp only [hvI]
    rw [Finset.prod_mul_distrib]
    congr 2
    calc (cinf : ℝ≥0∞) * (∫⁻ Y, φinf Y ∂minf') *
          ((∏ v ∈ S, (c v : ℝ≥0∞)) * ∏ v ∈ S, ∫⁻ Y, φ v Y ∂(m' v))
        = ((cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞)) *
            ((∫⁻ Y, φinf Y ∂minf') * ∏ v ∈ S, ∫⁻ Y, φ v Y ∂(m' v)) := by ring
      _ = _ := by rw [hone, one_mul]

end GlobalTheory.CompanionTheory.SW.EulerMove
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuotientProbabilityMeasure
section
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem isProbabilityMeasure_prH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsProbabilityMeasure (prH μ 𝓕) := by
  intro F E _ _ _ _ _ σ hσ M J hJ μ 𝓕 hμ h𝓕
  have hfin : μ 𝓕 < ⊤ := ((_root_.GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hσ M J hJ).2 μ hμ).2 𝓕 h𝓕
  obtain ⟨hlc, hsc, ht2⟩ := (GlobalTheory.CompanionTheory.AdeleTop.adele_top F).1
  obtain ⟨htg, hlcH, hscH, ht2H, hbor, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hσ M J hJ (AF F)
  have hcount : Countable (HFinIn (AF F) σ J) := (_root_.GlobalTheory.CompanionTheory.SW.rational_countable_discrete F E σ hσ M J hJ).1
  have hne : μ 𝓕 ≠ 0 :=
    (@GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain (HA (AF F) σ J) _ _ htg ht2H hlcH hscH _ hbor
      (HFinIn (AF F) σ J) hcount μ hμ 𝓕 h𝓕 hfin).1
  refine ⟨?_⟩
  simp only [prH, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hne hfin.ne

end GlobalTheory.CompanionTheory.SW.BB
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_adelic_character : ∀ (F : Type) [Field F] [NumberField F], (∃ ψ : AddChar (A F) ℂ, IsStdChar F ψ) ∧ ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → (∀ x, ‖ψ x‖ = 1) ∧ (∀ x ∈ Oh F, ψ x = 1) ∧ ∀ b : F, (∀ x ∈ Oh F, ψ (algebraMap F (A F) b * x) = 1) ↔ ∀ r : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (b * (r : F)) = n := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.StdChar.main | exact GlobalTheory.CompanionTheory.SW.Core.StdChar.main | (intros; apply GlobalTheory.CompanionTheory.SW.Core.StdChar.main <;> assumption)
end

