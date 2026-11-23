module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureExtensionByScalar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0096
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0663
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0666
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0661
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0688
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0685
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0694
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0675
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0424
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0456
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0693

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeExtendByScalarBlock
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.Aniso

theorem free_inf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)) (hlam : lam.IsAddHaarMeasure) (n : ℕ) :
    ∃ m, IsGramFibFree (Ainf F) σ J n (coordW (Ainf F) b lam n M) (coordHerm (Ainf F) σ b lam n) m := by
  have hB : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨-, hW, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Ainf F) _ b lam hlam
  exact _root_.GlobalTheory.ArchGramFibre.exists_fibreFamily F E σ hCM M n J hJ _ _ (hW n M) (hH n)

theorem free_v {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v))
    (hlam : lam.IsAddHaarMeasure) (n : ℕ) :
    ∃ m, IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m := by
  have := PI.VolStabS.secondCountable_Fv F v
  have := PI.VolStabS.locallyCompact_Fv F v
  have hB : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, hW, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Fv F v) _ b lam hlam
  exact PI.OmFibreUniq.W.gram_map_fibre_existence σ J v n hCM hJ _ _ (hW n M) (hH n)

theorem good_mass_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b) (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam : Measure (Fv F v), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree (Fv F v) σ (blockOne (algebraMap F E t) J) (n + 1) (coordW (Fv F v) b lam (n + 1) (M + 1)) (coordHerm (Fv F v) σ b lam (n + 1)) m → IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) 1 (coordW (Fv F v) b lam 1 (M + 1)) (coordHerm (Fv F v) σ b lam 1) m₁ → IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → ∀ c : ℝ≥0, (coordK (Fv F v) b lam).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) = c • coordK (Fv F v) b lam → m (hermOf (Fv F v) σ _ hT') (latV b v) = (c : ℝ≥0∞) ^ n * (m' (hermOf (Fv F v) σ T hT) (latV b v) * m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)) (latV b v)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hT' d b
  obtain ⟨hdet, hherm, -, -⟩ := BlockAlg.block_alg F E σ hCM M J t
  have hND : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hherm hJ.1, by
      rw [hdet]
      exact mul_ne_zero (by simpa using ht) hJ.2⟩
  filter_upwards [_root_.GlobalTheory.CompanionTheory.SW.StageGoodFree.stage_good_free F E σ hCM M J hJ t ht n T hT d b] with v hv
  intro lam hlam m m₁ m' hm hm₁ hm' c hc
  have hLoc := LocFv.isLocR_Fv F v
  obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := id hLoc
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  have hH := coord_measures_haar F E σ hCM (Fv F v) d b lam hlam
  obtain ⟨hring, -, -, -, -, -, -, hB, -, -⟩ := TopK.topTens_props F E σ hCM (Fv F v)
  have hlat : ∀ n' M' : ℕ, MeasurableSet (latV b v : Set (Fin n' → Fin M' → Fv F v ⊗[F] E)) := by
    intro n' M'
    haveI := hB n' M'
    exact ((MeasProj.proj_props F E σ hCM d b n' M').2.2.2.1 v).2.measurableSet
  obtain ⟨Ψ, -, hΨ, hint⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeStage.fibre_block_stages_free F E σ hCM M J hJ t ht n T hT hT' (Fv F v) hLoc d b lam hlam
    m m₁ m' hm hm₁ hm' c hc ((latV b v).indicator 1) (measurable_one.indicator (hlat _ _))
  set A := m' (hermOf (Fv F v) σ T hT) (latV b v) with hA
  have hae : Ψ =ᵐ[m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))] (latV b v).indicator (fun _ => A) := by
    filter_upwards [mem_ae_iff.2 (hm₁.1 (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))] with y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hg : gramR (Fv F v) σ (blockOne (algebraMap F E t) J)
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) =
        gramR (Fv F v) σ (blockOne (algebraMap F E t) J) y :=
      (StageGood.gram_first (Fv F v) σ J t).trans hy1.symm
    obtain ⟨h, rfl⟩ := _root_.GlobalTheory.CompanionTheory.SW.WittTuples.exists_actW_eq_of_gramR_eq F E σ hCM (M + 1) _ hND (Fv F v) 1 _ y hg
      (by rw [hg]; exact hy2)
    rw [hΨ h]
    haveI := hB n M
    haveI := hB (n + 1) (M + 1)
    have hS : MeasurableSet {X : Fin n → Fin M → Fv F v ⊗[F] E |
        actW (Fv F v) σ _ h (consTup X) ∈ latV b v} :=
      (GoodMass.continuous_act_consTup (Fv F v) hring σ _ h).measurable (hlat _ _)
    have hfun : (fun X : Fin n → Fin M → Fv F v ⊗[F] E =>
        (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ _ h (consTup X))) =
        {X | actW (Fv F v) σ _ h (consTup X) ∈ latV b v}.indicator 1 := by
      funext X
      rfl
    rw [hfun, lintegral_indicator_one hS, hv _ _ m' (hH.2.1 n M) (hH.2.2 n) hm' h]
  rw [← lintegral_indicator_one (hlat _ _), hint, lintegral_congr_ae hae,
    lintegral_indicator_const (hlat _ _)]

theorem summable_mul_sub_one {ι : Type} {x y : ι → ℝ} (hx : Summable fun i => |x i - 1|)
    (hy : Summable fun i => |y i - 1|) : Summable fun i => |x i * y i - 1| := by
  have ht : ∀ᶠ i in Filter.cofinite, |y i - 1| < 1 := by
    have := hy.tendsto_cofinite_zero
    exact this.eventually (gt_mem_nhds one_pos)
  refine Summable.of_norm_bounded_eventually (g := fun i => 2 * |x i - 1| + |y i - 1|)
    ((hx.mul_left 2).add hy) ?_
  filter_upwards [ht] with i hi
  have e : x i * y i - 1 = (x i - 1) * (y i - 1) + (x i - 1) + (y i - 1) := by ring
  rw [Real.norm_eq_abs, abs_abs, e]
  have h1 : |(x i - 1) * (y i - 1)| ≤ |x i - 1| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hi.le
  calc _ ≤ |(x i - 1) * (y i - 1) + (x i - 1)| + |y i - 1| := abs_add_le _ _
    _ ≤ |(x i - 1) * (y i - 1)| + |x i - 1| + |y i - 1| := by gcongr; exact abs_add_le _ _
    _ ≤ 2 * |x i - 1| + |y i - 1| := by linarith

theorem aniso_step : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ n : ℕ, 2 * n + 1 < M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), (framesE σ J T).Nonempty → SWFree σ J T hT → SWFree σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T) hT' := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n hn T hT hT' _ hSW d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  classical
  have hLi : IsLocR (Ainf F) := _root_.GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have hta : algebraMap F E t ≠ 0 := by simpa using ht
  obtain ⟨hdetb, hhermb, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hCM M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hhermb hJ.1, by rw [hdetb]; exact mul_ne_zero hta hJ.2⟩

  obtain ⟨m₁inf, hm₁inf⟩ := Step.loc_families σ hCM _ hJ' (Ainf F) hLi b laminf hinf.1 1
  obtain ⟨m'inf, hm'inf⟩ := free_inf σ hCM J hJ b laminf hinf.1 n
  choose m₁ hm₁ using fun v => Step.loc_families σ hCM _ hJ' (Fv F v) (hLv v) b (lam v) (hlam v).1 1
  choose m' hm' using fun v => free_v σ hCM J hJ b v (lam v) (hlam v).1 n
  obtain ⟨⟨μ₁, hμ₁⟩, hFV⟩ := _root_.GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM M J hJ
  obtain ⟨⟨𝓕₁, h𝓕₁⟩, -⟩ := hFV μ₁ hμ₁

  obtain ⟨cinf, c, hc, hcinf, hcv⟩ := _root_.GlobalTheory.CompanionTheory.SW.map_inclR_prodFormula F E σ hCM (algebraMap F E t) hta
  have hKi : (coordK (Ainf F) b laminf).map (fun y => inclR (Ainf F) (algebraMap F E t) * y) =
      cinf • coordK (Ainf F) b laminf := by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLi
    exact hcinf _ (_root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Ainf F) d b laminf hinf.1).1
  have hKv : ∀ v, (coordK (Fv F v) b (lam v)).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) =
      c v • coordK (Fv F v) b (lam v) := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    exact hcv v _ (_root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Fv F v) d b (lam v) (hlam v).1).1
  obtain ⟨-, -, -, -, -, -, -, S₃, hS₃⟩ := _root_.GlobalTheory.CompanionTheory.SW.UnitProdAlg.main F cinf 1 c (fun _ => 1) hc ⟨by simp, by simp⟩

  have hE' := hSW d b laminf lam hinf hlam μ₁ 𝓕₁ hμ₁ h𝓕₁ m'inf (fun v => m' v) hm'inf hm'
  let T1 : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E t
  have hT1 : ∀ a b, σ (T1 b a) = T1 a b := fun a b => by simp [T1]
  have hdet1 : T1.det ≠ 0 := by rw [Matrix.det_fin_one]; exact hta
  have hE₁ := _root_.GlobalTheory.CompanionTheory.SW.OneVector.siegel_one_vector F E σ hCM (M + 1) _ hJ' (by omega) T1 hT1 hdet1 d b laminf lam hinf hlam μ 𝓕 hμ h𝓕
    m₁inf m₁ hm₁inf hm₁
  obtain ⟨β, hβ1, -, hβ2⟩ := _root_.GlobalTheory.CompanionTheory.SW.hermOne_eq_scal F E σ hCM T1 hT1
  have hβ : β = t := (algebraMap F E).injective (congrFun (congrFun hβ1 0) 0).symm
  rw [hβ] at hβ2
  simp only [hβ2] at hE₁
  obtain ⟨-, hsum₁, S₁, hS₁⟩ := hE₁
  have hsum' := hE'.2.1
  have hG := good_mass_free F E σ hCM M J hJ t ht n T hT hT' d b
  have hgood₁ : ∀ v, m v (hermOf (Fv F v) σ _ hT') (latV b v) < ⊤ := fun v =>
    _root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.compact_finite_block F E σ hCM M J hJ t ht n T hT hT' (Fv F v) (hLv v) d b (lam v) (hlam v).1 (m v) (m₁ v) (m' v)
      (hm v) (hm₁ v) (hm' v) (c v) (hKv v)
      (_root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt.fibre_compact_lt_top F E σ hCM M J hJ n T hT hSW d b laminf lam hinf hlam v (m' v) (hm' v)) _
      ((_root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hCM d b (n + 1) (M + 1)).2.2.2.1 v).1
  have hgood₂ : Summable fun v => |(m v (hermOf (Fv F v) σ _ hT') (latV b v)).toReal - 1| := by
    have hP := summable_mul_sub_one hsum' hsum₁
    refine (summable_congr_cofinite ?_).1 hP
    filter_upwards [hG, hc.1] with v hv hcv1
    rw [hv (lam v) (hlam v).1 (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v) (c v) (hKv v), hcv1]
    simp [ENNReal.toReal_mul]
  refine ⟨hgood₁, hgood₂, ?_⟩
  obtain ⟨S₂, hS₂⟩ := Step.theta_hypothesis F E σ hCM M J hJ t ht n d b _ _ _ hE'
  have hSG := _root_.GlobalTheory.CompanionTheory.SW.StageGoodFree.stage_good_free F E σ hCM M J hJ t ht n T hT d b
  refine ⟨S₁ ∪ S₂ ∪ S₃ ∪ (Filter.eventually_cofinite.1 hG).toFinset ∪ (Filter.eventually_cofinite.1 hSG).toFinset,
    fun S hS φinf φ hφinf hφ => ?_⟩
  have hS1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  have hS2 : S₂ ⊆ S := fun x hx => hS (by simp [hx])
  have hS3 : S₃ ⊆ S := fun x hx => hS (by simp [hx])
  have hS4 : (Filter.eventually_cofinite.1 hG).toFinset ⊆ S := fun x hx => hS (by
    simp only [Finset.mem_union]; exact Or.inl (Or.inr hx))
  have hS5 : (Filter.eventually_cofinite.1 hSG).toFinset ⊆ S := fun x hx => hS (by
    simp only [Finset.mem_union]; exact Or.inr hx)
  obtain ⟨hc1, hc2⟩ := hS₃ S hS3
  obtain ⟨Ψinf, hΨinfm, hΨinf1, hΨinf2⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeStage.fibre_block_stages_free F E σ hCM M J hJ t ht n T hT hT' (Ainf F) hLi d b
    laminf hinf.1 minf m₁inf m'inf hminf hm₁inf hm'inf cinf hKi φinf hφinf
  choose Ψ hΨm hΨ1 hΨ2 using fun v => _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeStage.fibre_block_stages_free F E σ hCM M J hJ t ht n T hT hT' (Fv F v) (hLv v) d b
    (lam v) (hlam v).1 (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v) (c v) (hKv v) (φ v) (hφ v)
  have hHv : ∀ v, (coordW (Fv F v) b (lam v) n M).IsAddHaarMeasure ∧ (coordHerm (Fv F v) σ b (lam v) n).IsAddHaarMeasure := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    have hh := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    exact ⟨hh.2.1 n M, hh.2.2 n⟩
  have hHyp := hS₂ S hS2 φinf φ Ψinf Ψ hφinf hφ hΨinf1 hΨ1 (fun v hv g =>
    Step.of_cofinite hSG hS5 hv _ _ (m' v) (hHv v).1 (hHv v).2 (hm' v) g)
  set τ' := ENNReal.ofReal (∏' v : {v // v ∉ S}, (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal) with hτ'
  have hPm : Measurable (pureL b S Ψinf Ψ) := _root_.GlobalTheory.CompanionTheory.SW.PureMeas.measurable_pureL F E σ hCM d b 1 (M + 1) S Ψinf Ψ hΨinfm hΨm
  have hth := _root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.FrameTheta.theta_stage_frames F E σ hCM M J hJ t ht n T μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ (pureL b S φinf φ)
    (fun y => τ' * pureL b S Ψinf Ψ y) (_root_.GlobalTheory.CompanionTheory.SW.PureMeas.measurable_pureL F E σ hCM d b (n + 1) (M + 1) S φinf φ hφinf hφ)
    (hPm.const_mul τ') hHyp
  have hone := hS₁ S hS1 Ψinf Ψ hΨinfm hΨm
  rw [hth, lintegral_const_mul _ hPm]
  have hone' : ∫⁻ X, pureL b S Ψinf Ψ X ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) = _ := hone
  rw [hone']
  have hprod : (∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ _ hT'))) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ _ hT')) =
      (∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) *
        ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))) := by
    have hone2 : (cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞) = 1 := by exact_mod_cast hc2
    rw [hΨinf2, Finset.prod_congr rfl (fun v _ => hΨ2 v), Finset.prod_mul_distrib, Finset.prod_pow]
    calc _ = ((cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞)) ^ n * ((∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) *
        ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))) := by rw [mul_pow]; ring
      _ = _ := by rw [hone2, one_pow, one_mul]
  have htail : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ _ hT') (latV b v.1)).toReal) =
      τ' * ENNReal.ofReal (∏' v : {v // v ∉ S}, (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal) := by
    have hA := _root_.GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {v // v ∉ S} (fun v => (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal)
      (hsum'.subtype _)
    have hB := _root_.GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {v // v ∉ S} (fun v => (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal)
      (hsum₁.subtype _)
    have hcong : ∀ v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ _ hT') (latV b v.1)).toReal =
        (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal * (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal := fun v => by
      rw [Step.of_cofinite hG hS4 v.2 (lam v.1) (hlam v.1).1 (m v.1) (m₁ v.1) (m' v.1) (hm v.1) (hm₁ v.1) (hm' v.1) (c v.1) (hKv v.1), hc1 v.1 v.2]
      simp [ENNReal.toReal_mul]
    rw [tprod_congr hcong, hA.1.tprod_mul hB.1, ENNReal.ofReal_mul (hA.2.2.2 fun _ => ENNReal.toReal_nonneg)]
  rw [hprod, htail]
  simp only [ENNReal.coe_one, one_mul]
  ring

end GlobalTheory.CompanionTheory.WeilSiegel.Free.Aniso
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaConvergenceOfSiegelSet
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilTheta

theorem weilThetaConvergence_of_siegelSet (hRT : GlobalTheory.Published.SiegelSetUnitary) : GlobalTheory.Published.WeilThetaConvergence := by
  intro D n V _hn hV θ hθ ν hν Φ
  obtain ⟨hcontΦ, -⟩ := _root_.GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ V.rank n Φ.1 Φ.2
  obtain ⟨r, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame (GlobalTheory.AdelicU.isCMExt_host D) (isHermND_gram V)
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hRT D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) V.rank V.gram (isHermND_gram V) r Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas ν hν
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.CompanionTheory.SiegelTheta.absTheta_le_torus D θ hθ V n Φ.1 Φ.2 Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hconj
  set S := GlobalTheory.SiegelSet.siegelSet D.sp.cm.sig V.gram Xf Yf Ω c K with hSdef
  have hSm : MeasurableSet S := hcl.measurableSet
  have hScov : ∀ g, ∃ γ ∈ GQ V, γ * g ∈ S := fun g => by
    obtain ⟨γ, hγ, s, hs, e⟩ := hcov g
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    rw [e, inv_mul_cancel_left]
    exact hs
  have hI : ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
      ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
        ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹) < ⊤ := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      exact GlobalTheory.CompanionTheory.SiegelCone.cone_integral_zero_vars_lt_top D.host.F V.rank (2 * n) c
    · have hw := GlobalTheory.T.witt_frame_rank_le_witt_index D V Xf Yf hW
      have h2 : n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank := hV.resolve_left (by omega)
      exact _root_.GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top D.host.F V.rank r (2 * n) hc (by omega)
  calc absThetaInt V ν Φ.1 ≤ ∫⁻ g in S, absTheta V Φ.1 g ∂ν :=
        GlobalTheory.T.theta_integral_le_fundamental_set D V ν hν Φ.1 hcontΦ S hSm hScov
    _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
          ENNReal.ofReal (max C 0 * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
            ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹) := by
        refine hC₁ (absTheta V Φ.1) _ (by fun_prop) fun p hp t ht a ha k hk => ?_
        have ht0 : ∀ i, 0 < t i := ht.1
        have hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n)) :=
          Finset.prod_nonneg fun i _ => pow_nonneg (ht0 i).le _
        refine (hC p hp t ht a ha k hk).trans (ENNReal.ofReal_le_ofReal ?_)
        gcongr
        exact le_max_left _ _
    _ = C₁ * (ENNReal.ofReal (max C 0) * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
          ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
            ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_congr fun t => by rw [ENNReal.ofReal_mul (le_max_right _ _), mul_assoc]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI)

end GlobalTheory.CompanionTheory.WeilTheta

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesVanishesLargeModule
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.BasePsi

theorem exists_bound_inf {F : Type} [Field F] [NumberField F] (C : Set (Ainf F)) (hC : IsCompact C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ C, ∏ w : InfinitePlace F, ‖y w‖ ^ w.mult ≤ B := by
  have hc : Continuous fun y : Ainf F => ∏ w : InfinitePlace F, ‖y w‖ ^ w.mult :=
    continuous_finsetProd _ fun w _ => ((continuous_apply w).norm).pow _
  obtain ⟨B, hB⟩ := (hC.image hc).bddAbove
  exact ⟨max B 0, le_max_right _ _, fun y hy => (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩

theorem exists_bound_fin {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (C : Set (Fv F v)) (hC : IsCompact C) : ∃ B : ℝ, 1 ≤ B ∧ ∀ y ∈ C, ‖y‖ ≤ B := by
  obtain ⟨B, hB⟩ := (hC.image continuous_norm).bddAbove
  exact ⟨max B 1, le_max_right _ _, fun y hy => (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩

theorem md_le_of_bounds {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (B : ℝ) (c : HeightOneSpectrum (𝓞 F) → ℝ) (hc : ∀ v ∈ S, 1 ≤ c v) (b : (AF F)ˣ)
    (hinf : ∏ w : InfinitePlace F, ‖(b : AF F).1 w‖ ^ w.mult ≤ B)
    (hS : ∀ v ∈ S, ‖(b : AF F).2 v‖ ≤ c v)
    (hout : ∀ v, v ∉ S → (b : AF F).2 v ∈ v.adicCompletionIntegers F) :
    md b ≤ B * ∏ v ∈ S, c v := by
  have hfin := IdeleGroup.finite_mulSupport_norm (K := F) b
  set T : Finset (HeightOneSpectrum (𝓞 F)) := hfin.toFinset ∪ S with hT
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => ‖(b : AF F).2 v‖) ⊆ (T : Set _) := by
    intro v hv
    simp only [hT, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl hv
  have hfp : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(b : AF F).2 v‖ ≤ ∏ v ∈ S, c v := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    calc ∏ v ∈ T, ‖(b : AF F).2 v‖ ≤ ∏ v ∈ T, (if v ∈ S then c v else 1) := by
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ => ?_
          by_cases hv : v ∈ S
          · simpa [hv] using hS v hv
          · simpa [hv] using (Valued.toNormedField.norm_le_one_iff).2
              ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).1 (hout v hv))
      _ = ∏ v ∈ S, (if v ∈ S then c v else 1) := by
          refine (Finset.prod_subset Finset.subset_union_right fun v _ hv => ?_).symm
          simp [hv]
      _ = ∏ v ∈ S, c v := Finset.prod_congr rfl fun v hv => by simp [hv]
  have hcS : 0 ≤ ∏ v ∈ S, c v := Finset.prod_nonneg fun v hv => zero_le_one.trans (hc v hv)
  have hB0 : 0 ≤ ∏ w : InfinitePlace F, ‖(b : AF F).1 w‖ ^ w.mult :=
    Finset.prod_nonneg fun w _ => pow_nonneg (norm_nonneg _) _
  have hfp0 : 0 ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(b : AF F).2 v‖ :=
    finprod_nonneg fun _ => norm_nonneg _
  rw [md, IdeleGroup.ideleModule_eq]
  exact mul_le_mul hinf hfp hfp0 (hB0.trans hinf)

theorem th_pure_vanish : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), HasCompactSupport G → (∀ v ∈ S, HasCompactSupport (g v)) →
    ∃ R : ℝ, ∀ a : (AF F)ˣ, R < md a → th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) a = 0 := by
  intro F _ _ S G g hG hg
  obtain ⟨B, -, hB⟩ := exists_bound_inf (F := F) (tsupport G) hG
  have hfin : ∀ v ∈ S, ∃ B : ℝ, 1 ≤ B ∧ ∀ y ∈ tsupport (g v), ‖y‖ ≤ B :=
    fun v hv => exists_bound_fin v _ (hg v hv)
  choose! c hc1 hc using hfin
  refine ⟨B * ∏ v ∈ S, c v, fun a ha => ?_⟩
  by_contra hne
  obtain ⟨t, ht⟩ : ∃ t : Fˣ, PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) (pr t * a) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (by simp [th, hall])
  rw [pure_rv_zero_apply] at ht
  split_ifs at ht with hint
  · have hprod : G ((pr t * a : (AF F)ˣ) : AF F).1 * ∏ v ∈ S, g v (((pr t * a : (AF F)ˣ) : AF F).2 v) ≠ 0 :=
      fun h => ht (by rw [h]; simp)
    have hGne := left_ne_zero_of_mul hprod
    have hgne := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hprod)
    have hle := md_le_of_bounds S B c hc1 (pr t * a)
      (hB _ (subset_tsupport _ (Function.mem_support.2 hGne)))
      (fun v hv => hc v hv _ (subset_tsupport _ (Function.mem_support.2 (hgne v hv)))) hint
    rw [md_mul, md_pr, one_mul] at hle
    exact absurd ha (not_lt.2 hle)
  · exact ht rfl

end GlobalTheory.CompanionTheory.BasePsi

end
end

