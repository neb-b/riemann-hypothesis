module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRatFuncEmbeddingMoebius
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.Moebius

private theorem transcendental_of_mul_add_eq_mul {S K : Type*} [CommRing S] [IsDomain S] [Field K]
    [Algebra S K] {x t : K} {p q r : S} (hx : Transcendental S x)
    (hp : algebraMap S K p ≠ 0) (hr : algebraMap S K r ≠ 0)
    (h : t * (algebraMap S K p + x * algebraMap S K q) = x * algebraMap S K r) :
    Transcendental S t := by
  intro ht
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx isAlgebraic_zero
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact mul_ne_zero hx0 hr h.symm
  have hE : algebraMap S K r - t * algebraMap S K q ≠ 0 := by
    intro hE
    have h2 : t * algebraMap S K p = x * (algebraMap S K r - t * algebraMap S K q) := by
      linear_combination h
    rw [hE, mul_zero] at h2
    exact mul_ne_zero ht0 hp h2
  have hxe : x = t * algebraMap S K p * (algebraMap S K r - t * algebraMap S K q)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hE]
    linear_combination -h
  apply hx
  rw [hxe]
  exact (ht.mul (isAlgebraic_algebraMap p)).mul
    ((isAlgebraic_algebraMap r).sub (ht.mul (isAlgebraic_algebraMap q))).inv

theorem exists_ratFunc_embedding_moebius : ∀ (Φ S : Type) [Field Φ] [CommRing S] [IsDomain S] [Algebra Φ S] (p q r : S), p ≠ 0 → r ≠ 0 → ∃ θ : RatFunc Φ →+* FractionRing (Polynomial S), (∀ a, θ (algebraMap Φ (RatFunc Φ) a) = algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C (algebraMap Φ S a))) ∧ algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q) ≠ 0 ∧ θ RatFunc.X * (algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q)) = algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C r) := by
  intro Φ S _ _ _ _ p q r hp hr
  have hinj : Function.Injective (algebraMap (Polynomial S) (FractionRing (Polynomial S))) :=
    IsFractionRing.injective _ _
  have hs : ∀ s : S, algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C s) =
      algebraMap S (FractionRing (Polynomial S)) s := fun s => by
    rw [IsScalarTower.algebraMap_apply S (Polynomial S) (FractionRing (Polynomial S)),
      Polynomial.algebraMap_eq]
  have hpoly : Polynomial.C p + Polynomial.X * Polynomial.C q ≠ 0 := fun h =>
    hp (by simpa using congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f 0) h)
  have hD : algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q) ≠ 0 := by
    rw [← map_mul, ← map_add (f := _)]
    exact (map_ne_zero_iff _ hinj).2 hpoly
  obtain ⟨t, ht⟩ : ∃ t, t = algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C r) /
      (algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q)) := ⟨_, rfl⟩
  have htD : t * (algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q)) =
      algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C r) := by
    rw [ht]
    exact div_mul_cancel₀ _ hD
  have htr : Transcendental S t := by
    refine transcendental_of_mul_add_eq_mul (p := p) (q := q) (r := r)
      ((transcendental_algebraMap_iff hinj).2 (Polynomial.transcendental_X S)) ?_ ?_ ?_
    · rw [← hs]
      exact (map_ne_zero_iff _ hinj).2 (Polynomial.C_ne_zero.2 hp)
    · rw [← hs]
      exact (map_ne_zero_iff _ hinj).2 (Polynomial.C_ne_zero.2 hr)
    · simpa only [hs] using htD
  let φ : Polynomial Φ →+* FractionRing (Polynomial S) :=
    (Polynomial.aeval t).toRingHom.comp (Polynomial.mapRingHom (algebraMap Φ S))
  have hφinj : Function.Injective φ := by
    intro P Q hPQ
    apply Polynomial.map_injective _ (algebraMap Φ S).injective
    exact (transcendental_iff_injective.1 htr) hPQ
  have hφC : ∀ a : Φ, φ (Polynomial.C a) = algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C (algebraMap Φ S a)) := by
    intro a
    rw [hs]
    simp [φ]
  have hφX : φ Polynomial.X = t := by
    simp [φ]
  refine ⟨RatFunc.liftRingHom φ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφinj),
    fun a => ?_, hD, ?_⟩
  · rw [RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, RatFunc.liftRingHom_algebraMap, hφC]
  · rw [← RatFunc.algebraMap_X, RatFunc.liftRingHom_algebraMap, hφX, htD]

end GlobalTheory.CompanionTheory.Ar.Moebius
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapTorusInvariant
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem stepGap_torus : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ)
    (BM : BaseMetric M n) (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) (c : K → ℂ), (∀ k, c k ≠ 0) →
    (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → stepGap M BM p (fun q => c q.1 * z q) = stepGap M BM p z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p z c hc hz
  have hpos : 0 < ∏ k, ‖c k‖ ^ M.dy p k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc k)) _
  have h1 := (BM.hom p).smul c z hc
  rw [BM.hom_deg p] at h1
  have h2 : (fsHerm ι (M.dy p)).h (fun q => c q.1 * z q) =
      (∏ k, ‖c k‖ ^ M.dy p k) * (fsHerm ι (M.dy p)).h z := (fsHerm ι (M.dy p)).smul c z hc
  unfold stepGap
  rw [h1, h2, Real.log_mul hpos.ne' ((BM.hom p).pos z hz).ne',
    Real.log_mul hpos.ne' ((fsHerm ι (M.dy p)).pos z hz).ne']
  ring

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FubiniStudyMetricSmooth
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

theorem fsHerm_isSmoothHerm : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (a : K → ℤ), IsSmoothHerm (fsHerm ι a) :=
  fun _ _ _ _ a => GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm a

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramMatrixSubScalarPosSemidef
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

theorem gram_grad_scale_arith (D c P Q a : ℝ) (ha : 0 < a) (hP : 0 < P) (hQ : 0 < Q)
    (h : P / Q * D ≤ c * P ^ 3 / a) : D ≤ c * P ^ 2 * Q / a := by
  have h1 : D = Q / P * (P / Q * D) := by field_simp
  have h2 : 0 ≤ Q / P := (div_pos hQ hP).le
  calc D = Q / P * (P / Q * D) := h1
    _ ≤ Q / P * (c * P ^ 3 / a) := mul_le_mul_of_nonneg_left h h2
    _ = c * P ^ 2 * Q / a := by field_simp

theorem gram_grad_comp_smul (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x' : E) (a P t : ℝ)
    (ha : 0 < a) (hP : 0 < P)
    (h1 : ∀ p q, DifferentiableAt ℝ (fun y => G (t • y) p q) x')
    (h2 : ∀ p q, DifferentiableAt ℝ (fun y => V (t • y) p q) x')
    (h3 : ∀ᶠ y in nhds x', (G (t • y)).PosDef ∧ LinearIndependent ℂ (V (t • y))ᵀ)
    (h4 : ((V (t • x'))ᴴ * G (t • x') * V (t • x') -
      (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef)
    (h5 : ∀ p q, ‖G (t • x') p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => G (t • y) p q) x'‖ ≤ P)
    (h6 : ∀ p q, ‖V (t • x') p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => V (t • y) p q) x'‖ ≤ P) :
    ‖fderiv ℝ (fun y => Real.log ((V (t • y))ᴴ * G (t • y) * V (t • y)).det.re) x'‖ ≤
      3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * P ^ 3 / a :=
  _root_.GlobalTheory.CompanionTheory.Ar.PB.gram_logDet_fderiv_norm_le n k E (fun u => G (t • u)) (fun u => V (t • u)) x' a P ha hP.le h1 h2 h3 h4 h5 h6

theorem gram_grad_scaled : ∀ (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x : E) (a P Q : ℝ), 0 < a → 0 < P → P ≤ Q → (∀ p q, DifferentiableAt ℝ (fun y => G y p q) x) → (∀ p q, DifferentiableAt ℝ (fun y => V y p q) x) → (∀ᶠ y in nhds x, (G y).PosDef ∧ LinearIndependent ℂ (V y)ᵀ) → ((V x)ᴴ * G x * V x - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef → (∀ p q, ‖G x p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => G y p q) x‖ ≤ Q) → (∀ p q, ‖V x p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => V y p q) x‖ ≤ Q) → ‖fderiv ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x‖ ≤ 3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * P ^ 2 * Q / a := by
  intro n k E _ _ G V x a P Q ha hP hPQ hGd hVd hev hH hGb hVb
  have hQ : 0 < Q := lt_of_lt_of_le hP hPQ
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = P / Q := ⟨_, rfl⟩
  have ht0 : 0 < t := ht ▸ div_pos hP hQ
  have htne : t ≠ 0 := ht0.ne'
  obtain ⟨x', hx'⟩ : ∃ x' : E, x' = t⁻¹ • x := ⟨_, rfl⟩
  have hcx : t • x' = x := by rw [hx', smul_smul, mul_inv_cancel₀ htne, one_smul]
  have hL : DifferentiableAt ℝ (fun u : E => t • u) x' := (differentiableAt_id).const_smul t
  have hdiff : ∀ f : E → ℂ, DifferentiableAt ℝ f x →
      DifferentiableAt ℝ (fun u => f (t • u)) x' := by
    intro f hf
    have hf' : DifferentiableAt ℝ f (t • x') := by rw [hcx]; exact hf
    exact hf'.comp x' hL
  have hfd : ∀ f : E → ℂ, fderiv ℝ (fun u => f (t • u)) x' = t • fderiv ℝ f x := by
    intro f
    rw [fderiv_comp_smul, hcx]
  have hfdR : ∀ f : E → ℝ, fderiv ℝ (fun u => f (t • u)) x' = t • fderiv ℝ f x := by
    intro f
    rw [fderiv_comp_smul, hcx]
  have hbound : ∀ f : E → ℂ, ‖fderiv ℝ f x‖ ≤ Q →
      ‖fderiv ℝ (fun u => f (t • u)) x'‖ ≤ P := by
    intro f hf
    rw [hfd, norm_smul, Real.norm_of_nonneg ht0.le, ht]
    calc P / Q * ‖fderiv ℝ f x‖ ≤ P / Q * Q := mul_le_mul_of_nonneg_left hf (div_pos hP hQ).le
      _ = P := by field_simp
  have htend : Tendsto (fun u : E => t • u) (nhds x') (nhds x) := by
    have := hL.continuousAt.tendsto
    rwa [hcx] at this
  have key := gram_grad_comp_smul n k E G V x' a P t ha hP
    (fun p q => hdiff (fun y => G y p q) (hGd p q))
    (fun p q => hdiff (fun y => V y p q) (hVd p q))
    (htend.eventually hev)
    (by rw [hcx]; exact hH)
    (fun p q => ⟨by rw [hcx]; exact (hGb p q).1, hbound (fun y => G y p q) (hGb p q).2⟩)
    (fun p q => ⟨by rw [hcx]; exact (hVb p q).1, hbound (fun y => V y p q) (hVb p q).2⟩)
  have hk := hfdR (fun y => Real.log ((V y)ᴴ * G y * V y).det.re)
  rw [hk, norm_smul, Real.norm_of_nonneg ht0.le, ht] at key
  exact gram_grad_scale_arith _ _ P Q a ha hP hQ key

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloOnDivCongr
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem holoOn_eval {σ : Type} (A : FinHolAtlas e X) {W : Set X} {b : X → σ → ℂ}
    (hb : ∀ q, A.HoloOn W fun y => b y q) (p : MvPolynomial σ ℤ) :
    A.HoloOn W fun y => eval (b y) (map (Int.castRingHom ℂ) p) := by
  intro j
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [Function.comp_def] using
      (analyticOnNhd_const (v := ((a : ℤ) : ℂ)) (s := (A.chart j).target ∩ (A.chart j).symm ⁻¹' W))
  | add p q hp hq =>
    convert hp.add hq using 1
    funext u
    simp [Function.comp_def]
  | mul_X p q hp =>
    simpa [Function.comp_def] using hp.mul (hb q j)

theorem continuousAt_of_holoOn (A : FinHolAtlas e X) {W : Set X} {f : X → ℂ} (hf : A.HoloOn W f) {y : X}
    (hy : y ∈ W) : ContinuousAt f y := by
  obtain ⟨j, hj⟩ := A.cover y
  have h1 : (A.chart j) y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by
      rw [Set.mem_preimage, (A.chart j).left_inv hj]; exact hy⟩
  have h2 : ContinuousAt (f ∘ (A.chart j).symm) ((A.chart j) y) := (hf j _ h1).continuousAt
  have h3 : ContinuousAt (fun u => (f ∘ (A.chart j).symm) ((A.chart j) u)) y :=
    ContinuousAt.comp (f := A.chart j) h2 ((A.chart j).continuousAt hj)
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with u hu
  simp only [Function.comp_apply, (A.chart j).left_inv hu]

theorem isOpen_inter_ne (A : FinHolAtlas e X) {W : Set X} {f : X → ℂ} (hW : IsOpen W)
    (hf : A.HoloOn W f) : IsOpen (W ∩ {y | f y ≠ 0}) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hy, h0⟩
  filter_upwards [hW.mem_nhds hy, (continuousAt_of_holoOn A hf hy).eventually_ne h0] with u h1 h2
  exact ⟨h1, h2⟩

theorem holoOn_div_congr (A : FinHolAtlas e X) {W : Set X} {f g v : X → ℂ} (hW : IsOpen W)
    (hf : A.HoloOn W f) (hg : A.HoloOn W g) (h0 : ∀ y ∈ W, g y ≠ 0) (hv : ∀ y ∈ W, v y = f y / g y) :
    A.HoloOn W v := by
  intro j
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
    (A.chart j).isOpen_inter_preimage_symm hW
  have h1 : AnalyticOnNhd ℂ (fun u => (f ∘ (A.chart j).symm) u / (g ∘ (A.chart j).symm) u)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) := fun u hu =>
    (hf j u hu).div (hg j u hu) (h0 _ hu.2)
  exact h1.congr hO fun u hu => (hv _ hu.2).symm

theorem holoOn_valAt (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (x : (Σ k, ι k) → Ω) (s : Ω) (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (W : Set X)
    (b : X → (Σ k, ι k) → ℂ) (y₀ : X) (hW : IsOpen W) (hy₀ : y₀ ∈ W) (hb : ∀ q, A.HoloOn W fun y => b y q)
    (hpt : ∀ y ∈ W, b y ∈ mcPts (mCoordIdeal x)) (hs : RegAt x (mCoordIdeal (b y₀)) s) :
    ∃ W' : Set X, IsOpen W' ∧ y₀ ∈ W' ∧ W' ⊆ W ∧ A.HoloOn W' fun y => valAt x s (b y) := by
  obtain ⟨d, g, h, hg, hh, hQ, heq⟩ := hs
  have hz : eval (b y₀) (map (Int.castRingHom ℂ) h) ≠ 0 := by
    intro h0
    refine hQ (mem_mCoordIdeal_of_aeval_eq_zero (b y₀) hh ?_)
    rw [← h0]
    rw [aeval_def, eval_map, Subsingleton.elim (algebraMap ℤ ℂ) (Int.castRingHom ℂ)]
  have hx : aeval x h ≠ 0 := fun h0 =>
    hz (eval_eq_zero_of_mem_mcPts (hpt y₀ hy₀) (mem_mCoordIdeal_of_aeval_eq_zero x hh h0))
  have Hg := holoOn_eval A hb g
  have Hh := holoOn_eval A hb h
  refine ⟨W ∩ {y | eval (b y) (map (Int.castRingHom ℂ) h) ≠ 0}, isOpen_inter_ne A hW Hh, ⟨hy₀, hz⟩,
    Set.inter_subset_left, ?_⟩
  refine holoOn_div_congr A (isOpen_inter_ne A hW Hh) (fun j => (Hg j).mono ?_) (fun j => (Hh j).mono ?_)
    (fun y hy => hy.2) fun y hy => ?_
  · exact Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left)
  · exact Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left)
  · exact valAt_eq (hpt y hy.1) ⟨d, g, h, hg, hh, hx, heq, hy.2, rfl⟩

end GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicConjugatePullback
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

theorem analyticAt_conj_comp_star {e : ℕ} {h : (Fin e → ℂ) → ℂ} {u : Fin e → ℂ}
    (hh : AnalyticAt ℂ h (star u)) :
    AnalyticAt ℂ (fun v => starRingEnd ℂ (h (star v))) u := by
  have hc : ContinuousAt (star : (Fin e → ℂ) → (Fin e → ℂ)) u := continuous_star.continuousAt
  refine GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 ?_
  filter_upwards [hc.eventually hh.eventually_analyticAt] with q hq
  simpa [Function.comp_def] using hq.differentiableAt.star_star

theorem holoOn_conj_comp {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} (c : X → X)
    (hc : Continuous c)
    (hanti : ∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z))))
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source)))
    {V : Set X} {g : X → ℂ} (hg : A.HoloOn V g) :
    A.HoloOn (c ⁻¹' V) (fun y => starRingEnd ℂ (g (c y))) := by
  intro j w hw
  obtain ⟨k, hk⟩ := A.cover (c ((A.chart j).symm w))
  have hw' : w ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source) := ⟨hw.1, hk⟩
  have h1 := hanti j k w hw'
  have h2 : AnalyticAt ℂ (g ∘ (A.chart k).symm) (A.chart k (c ((A.chart j).symm w))) := by
    refine hg k _ ⟨(A.chart k).map_source hk, ?_⟩
    simp only [Set.mem_preimage, (A.chart k).left_inv hk]
    exact hw.2
  have h3 : AnalyticAt ℂ (fun v => starRingEnd ℂ ((g ∘ (A.chart k).symm) (star v)))
      (star (A.chart k (c ((A.chart j).symm w)))) :=
    analyticAt_conj_comp_star (by simpa using h2)
  have h4 := AnalyticAt.comp (g := fun v => starRingEnd ℂ ((g ∘ (A.chart k).symm) (star v)))
    (f := fun z => star (A.chart k (c ((A.chart j).symm z)))) (x := w) h3 h1
  refine h4.congr ?_
  have hcc : ContinuousAt (c ∘ (A.chart j).symm) w :=
    hc.continuousAt.comp ((A.chart j).continuousAt_symm hw.1)
  filter_upwards [hcc ((A.chart k).open_source.mem_nhds hk)] with w' hw''
  have hw3 : c ((A.chart j).symm w') ∈ (A.chart k).source := hw''
  simp [Function.comp, (A.chart k).left_inv hw3]

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicDegreeOneBiholomorphism
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

theorem exists_holoMap_inverse_of_degree_one : ∀ {e : ℕ} {X Y : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (A : FinHolAtlas e X) (B : FinHolAtlas e Y)
    (h : Y → X), HoloMap B A h → IsDegreeOff A B h 1 ∅ →
    ∃ g : X → Y, (∀ y, g (h y) = y) ∧ (∀ x, h (g x) = x) ∧ HoloMap A B g := by
  intro e X Y _ _ _ _ _ A B h hh hd
  obtain ⟨-, -, -, -, hfib, hdet⟩ := hd
  have hex : ∀ x, ∃ y, h ⁻¹' {x} = {y} := fun x => Set.ncard_eq_one.1 (hfib x (by simp))
  have hinj : Function.Injective h := by
    intro a b hab
    obtain ⟨c, hc⟩ := hex (h a)
    have ha : a ∈ h ⁻¹' {h a} := rfl
    have hb : b ∈ h ⁻¹' {h a} := hab.symm
    rw [hc] at ha hb
    exact ha.trans hb.symm
  have hsurj : Function.Surjective h := by
    intro x
    obtain ⟨c, hc⟩ := hex x
    have hcx : c ∈ h ⁻¹' {x} := by rw [hc]; rfl
    exact ⟨c, hcx⟩
  let E : Y ≃ X := Equiv.ofBijective h ⟨hinj, hsurj⟩
  have hEc : Continuous E := hh.1
  obtain ⟨g, hgE⟩ : ∃ g : X → Y, g = E.symm := ⟨_, rfl⟩
  have hgc : Continuous g := by
    rw [hgE]; exact hEc.homeoOfEquivCompactToT2.symm.continuous
  have hgh : ∀ y, g (h y) = y := fun y => by rw [hgE]; exact E.symm_apply_apply y
  have hhg : ∀ x, h (g x) = x := fun x => by rw [hgE]; exact E.apply_symm_apply x
  refine ⟨g, hgh, hhg, hgc, fun j k w hw => ?_⟩
  obtain ⟨hwt, hws⟩ := hw
  have hys : g ((A.chart j).symm w) ∈ (B.chart k).source := hws
  obtain ⟨v, hv⟩ : ∃ v, v = B.chart k (g ((A.chart j).symm w)) := ⟨_, rfl⟩
  have hvt : v ∈ (B.chart k).target := hv ▸ (B.chart k).map_source hys
  have hsv : (B.chart k).symm v = g ((A.chart j).symm w) := by
    rw [hv]; exact (B.chart k).left_inv hys
  have hhv : h ((B.chart k).symm v) ∈ (A.chart j).source := by
    rw [hsv, hhg]; exact (A.chart j).map_target hwt
  obtain ⟨T, hT⟩ : ∃ T : (Fin e → ℂ) → Fin e → ℂ, T = A.chart j ∘ h ∘ (B.chart k).symm := ⟨_, rfl⟩
  have hTa : AnalyticAt ℂ T v := by
    rw [hT]; exact hh.2 k j v ⟨hvt, hhv⟩
  have hTv : T v = w := by
    rw [hT]
    simp only [Function.comp_apply]
    rw [hsv, hhg]
    exact (A.chart j).right_inv hwt
  have hdet' : (fderiv ℂ T v).det ≠ 0 := by
    rw [hT]; exact hdet k j v hvt (by simp) hhv
  have hCe := ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero (fderiv ℂ T v) hdet'
  obtain ⟨Ce, hCedef⟩ : ∃ Ce, Ce = (fderiv ℂ T v).toContinuousLinearEquivOfDetNeZero hdet' := ⟨_, rfl⟩
  rw [← hCedef] at hCe
  have hstrict : HasStrictFDerivAt T (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) v := by
    rw [hCe]; exact hTa.hasStrictFDerivAt
  set F := hstrict.toOpenPartialHomeomorph T with hF
  have hFc : (F : (Fin e → ℂ) → (Fin e → ℂ)) = T := hstrict.toOpenPartialHomeomorph_coe
  have hus : v ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hsym : AnalyticAt ℂ F.symm w := by
    have h1 : AnalyticAt ℂ F.symm (F v) :=
      F.analyticAt_symm' (i := Ce) hus (by rw [hFc]; exact hTa) (by rw [hFc, hCe])
    rwa [hFc, hTv] at h1
  have hc2 : ContinuousAt (g ∘ (A.chart j).symm) w :=
    hgc.continuousAt.comp ((A.chart j).continuousAt_symm hwt)
  have hc : ContinuousAt (B.chart k ∘ g ∘ (A.chart j).symm) w :=
    ContinuousAt.comp (g := B.chart k) ((B.chart k).continuousAt hys) hc2
  have hus' : F.source ∈ nhds ((B.chart k ∘ g ∘ (A.chart j).symm) w) := by
    have : (B.chart k ∘ g ∘ (A.chart j).symm) w = v := hv.symm
    rw [this]; exact F.open_source.mem_nhds hus
  refine hsym.congr ?_
  filter_upwards [hc.preimage_mem_nhds hus',
    hc2.preimage_mem_nhds ((B.chart k).open_source.mem_nhds hys),
    (A.chart j).open_target.mem_nhds hwt] with w' h1 h2 h3
  have h2' : g ((A.chart j).symm w') ∈ (B.chart k).source := h2
  have e1 : T ((B.chart k ∘ g ∘ (A.chart j).symm) w') = w' := by
    rw [hT]
    simp only [Function.comp_apply]
    rw [(B.chart k).left_inv h2', hhg]
    exact (A.chart j).right_inv h3
  have e2 := F.left_inv h1
  rw [hFc, e1] at e2
  exact e2

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsClosedSectionBoundary
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.CWeight

theorem isClosed_bdry_of_isSection : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsSection A L s → IsClosed (bdry s) := by
  intro e X _ A L s hS
  exact ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology.isClosed_bdry hS

end GlobalTheory.CompanionTheory.Ar.PB.CWeight
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MCoordIdealCompLeImageZ
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.FA.ImageIdeal

theorem mCoordIdeal_comp_le_imageZ : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K']
    (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K' → K) (v : (Σ k, ι' k) → Σ k, ι k) (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ), IsBlockMap κ v → mCoordIdeal (y ∘ v) ≤ imageZ v (mCoordIdeal y) := by
  intro K _ ι _ K' _ ι' _ κ v Φ _ y hv f hf
  have key : ∀ g : MRing ι', mConeMap y (rename v g) = rename κ (mConeMap (y ∘ v) g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, hv.2.2.1 n]
  have hf' : mConeMap (y ∘ v) f = 0 := hf
  show mConeMap y (rename v f) = 0
  rw [key, hf', map_zero]

end GlobalTheory.CompanionTheory.Ar.PB.FA.ImageIdeal
end

