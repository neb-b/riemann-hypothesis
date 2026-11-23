module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0139
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalTwoSided
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsFolnerSequenceBessel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryFrameDual
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsInnerLatticeImageFrameQuotient
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0230

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralEqOfQuotientMeasuresBesselUnitary
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SnMass.QuotUniq

theorem lintegral_le {k r : ℕ} {R : Set (Mat k r)} {μG μR ν ν' : Measure (Mt k r)}
    (hR : IsClosedSub k r R) (hG : IsHaarOn (GG k r) μG) (hμ : IsHaarOn R μR) (hU : IsUnimod R μR)
    (hν : IsQuotMeas μG μR ν) (hν' : IsQuotMeas μG μR ν') (F : Mt k r → ℝ≥0∞) (hF : Measurable F)
    (hFi : ∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → F (lmulM ρ x) = F x) :
    ∫⁻ x, F x ∂ν ≤ ∫⁻ x, F x ∂ν' := by
  obtain ⟨-, -, φ, hφ, h⟩ := GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν hR hG hμ hU hν
  obtain ⟨h1, -, -⟩ := GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν' hR hG hμ hU hν'
  have h1' : ∀ᵐ x ∂ν', Matrix.of x ∈ GG k r := h1
  have hae : ∀ᵐ s ∂μR, Matrix.of s ∈ R := hμ.2.2.1
  have hW' : ∀ f : Mt k r → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (lmulM (Matrix.of s) x) ∂μR) ∂ν' := hν'
  have hTm := (GlobalTheory.Amp.CutQuot.continuous_act k r).measurable
  rw [h F hF hFi, hW' (fun x => φ x * F x) (hφ.1.mul hF)]
  refine lintegral_mono_ae ?_
  filter_upwards [h1'] with x hx
  have hTx : Measurable fun s : Mt k r => lmulM (Matrix.of s) x :=
    hTm.comp (measurable_id.prodMk measurable_const)
  have h2 : ∫⁻ s, φ (lmulM (Matrix.of s) x) * F (lmulM (Matrix.of s) x) ∂μR =
      ∫⁻ s, φ (lmulM (Matrix.of s) x) * F x ∂μR := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with s hs
    rw [hFi _ hs x hx]
  rw [h2, lintegral_mul_const (F x) (f := fun s => φ (lmulM (Matrix.of s) x)) (hφ.1.comp hTx)]
  exact mul_le_of_le_one_left zero_le (hφ.2 x hx)

theorem quot_uniq : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν ν' : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → IsQuotMeas μG μR ν' → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (F : Mat k r → V), ContinuousOn F (GG k r) → (∀ ρ ∈ R, ∀ x ∈ GG k r, F (ρ * x) = F x) → (Integrable (fun x : Mt k r => F (Matrix.of x)) ν ↔ Integrable (fun x : Mt k r => F (Matrix.of x)) ν') ∧ ∫ x, F (Matrix.of x) ∂ν = ∫ x, F (Matrix.of x) ∂ν' := by
  intro k r R μG μR ν ν' hR hG hμ hU hν hν' V _ _ _ F hF hFi
  classical
  borelize V
  set S : Set (Mt k r) := {x | Matrix.of x ∈ GG k r} with hS
  have hSm : MeasurableSet S := GlobalTheory.Amp.CutQuot.measurable_G k r
  have hFc : ContinuousOn (fun x : Mt k r => F (Matrix.of x)) S := hF
  set F' : Mt k r → V := S.piecewise (fun x : Mt k r => F (Matrix.of x)) (fun _ => 0) with hF'
  have hF'm : Measurable F' := hFc.measurable_piecewise continuousOn_const hSm
  have hsep : TopologicalSpace.IsSeparable (Set.range F') := by
    have h1 : TopologicalSpace.IsSeparable ((fun x : Mt k r => F (Matrix.of x)) '' S) :=
      hFc.isSeparable_image (TopologicalSpace.IsSeparable.of_separableSpace S)
    refine (h1.union (Set.finite_singleton (0 : V)).isSeparable).mono ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ S
    · exact Or.inl ⟨x, hx, by rw [hF', Set.piecewise_eq_of_mem _ _ _ hx]⟩
    · exact Or.inr (by rw [hF', Set.piecewise_eq_of_notMem _ _ _ hx]; rfl)
  have hinv : ∀ ρ ∈ R, ∀ x : Mt k r, Matrix.of x ∈ GG k r → F' (lmulM ρ x) = F' x := by
    intro ρ hρ x hx
    have hx' : lmulM ρ x ∈ S := (GlobalTheory.Amp.CutQuot.mul_mem_iff (hR.1 hρ) (Matrix.of x)).2 hx
    rw [hF', Set.piecewise_eq_of_mem _ _ _ hx', Set.piecewise_eq_of_mem _ _ _ (show x ∈ S from hx)]
    exact hFi ρ hρ _ hx
  have hm : MeasurableSpace.comap F' inferInstance ≤ (inferInstance : MeasurableSpace (Mt k r)) :=
    hF'm.comap_le
  have hsm : StronglyMeasurable[MeasurableSpace.comap F' inferInstance] F' :=
    (@stronglyMeasurable_iff_measurable_separable _ _ _ (MeasurableSpace.comap F' inferInstance)
      _ _ _ _).2 ⟨comap_measurable F', hsep⟩
  have htrim : ν.trim hm = ν'.trim hm := by
    refine @Measure.ext _ (MeasurableSpace.comap F' inferInstance) _ _ fun A hA => ?_
    rw [trim_measurableSet_eq hm hA, trim_measurableSet_eq hm hA]
    have hAm : MeasurableSet A := hm A hA
    obtain ⟨B, -, rfl⟩ := hA
    have hi : ∀ ρ ∈ R, ∀ x : Mt k r, Matrix.of x ∈ GG k r →
        (F' ⁻¹' B).indicator (1 : Mt k r → ℝ≥0∞) (lmulM ρ x) = (F' ⁻¹' B).indicator 1 x := by
      intro ρ hρ x hx
      simp only [Set.indicator, Set.mem_preimage, hinv ρ hρ x hx, Pi.one_apply]
    rw [← lintegral_indicator_one hAm, ← lintegral_indicator_one hAm]
    exact le_antisymm (lintegral_le hR hG hμ hU hν hν' _ (measurable_one.indicator hAm) hi)
      (lintegral_le hR hG hμ hU hν' hν _ (measurable_one.indicator hAm) hi)
  have hae : ∀ ν₀ : Measure (Mt k r), IsQuotMeas μG μR ν₀ →
      (fun x : Mt k r => F (Matrix.of x)) =ᵐ[ν₀] F' := by
    intro ν₀ h
    have h1 : ∀ᵐ x ∂ν₀, x ∈ S := (GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν₀ hR hG hμ hU h).1
    filter_upwards [h1] with x hx
    rw [hF', Set.piecewise_eq_of_mem _ _ _ hx]
  rw [integrable_congr (hae ν hν), integrable_congr (hae ν' hν'), integral_congr_ae (hae ν hν),
    integral_congr_ae (hae ν' hν'), integral_trim hm hsm, integral_trim hm hsm, htrim]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, rfl⟩
  · exact integrable_of_integrable_trim hm (htrim ▸ h.trim hm hsm)
  · exact integrable_of_integrable_trim hm (htrim.symm ▸ h.trim hm hsm)

end GlobalTheory.SnMass.QuotUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanCovolumeFunction
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.FlagBase.MeanCov

theorem lintegral_div_inv (κ : ℝ) (hκ : 0 < κ) (w : ℝ → ENNReal) :
    ∫⁻ t in Set.Ioi (0 : ℝ), w (κ / t) / ENNReal.ofReal t
      = ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal t := by
  have himg : (fun t : ℝ => κ / t) '' Set.Ioi 0 = Set.Ioi 0 := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact div_pos hκ ht
    · intro hs
      have hs0 : s ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hs)
      refine ⟨κ / s, div_pos hκ hs, ?_⟩
      field_simp
  have hder : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun t : ℝ => κ / t) (κ * -(t ^ 2)⁻¹) (Set.Ioi 0) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ht)
    have h1 : HasDerivAt (fun y : ℝ => κ * y⁻¹) (κ * -(t ^ 2)⁻¹) t := (hasDerivAt_inv ht0).const_mul κ
    have h2 : (fun y : ℝ => κ / y) = fun y => κ * y⁻¹ := by
      funext y
      rw [div_eq_mul_inv]
    rw [h2]
    exact h1.hasDerivWithinAt
  have hinj : Set.InjOn (fun t : ℝ => κ / t) (Set.Ioi 0) := by
    intro a ha b hb hab
    have ha0 : a ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ha)
    have hb0 : b ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hb)
    have hk0 : κ ≠ 0 := ne_of_gt hκ
    simp only at hab
    field_simp at hab
    nlinarith [hab]
  have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj
    (fun s => w (κ / s) / ENNReal.ofReal s)
  rw [himg] at key
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  have ht' : 0 < t := Set.mem_Ioi.mp ht
  have hq : 0 < κ / t := div_pos hκ ht'
  have habs : |κ * -(t ^ 2)⁻¹| = κ / t * t⁻¹ := by
    rw [abs_mul, abs_neg, abs_of_pos hκ, abs_of_pos (by positivity)]
    field_simp
  have hkk : κ / (κ / t) = t := by
    field_simp
  simp only
  rw [habs, hkk, ENNReal.ofReal_mul hq.le, ENNReal.ofReal_inv_of_pos ht', div_eq_mul_inv, div_eq_mul_inv]
  have hne : ENNReal.ofReal (κ / t) ≠ 0 := by simpa using hq
  calc ENNReal.ofReal (κ / t) * (ENNReal.ofReal t)⁻¹ * (w t * (ENNReal.ofReal (κ / t))⁻¹)
      = (ENNReal.ofReal (κ / t) * (ENNReal.ofReal (κ / t))⁻¹) * (w t * (ENNReal.ofReal t)⁻¹) := by ring
    _ = w t * (ENNReal.ofReal t)⁻¹ := by
      rw [ENNReal.mul_inv_cancel hne ENNReal.ofReal_ne_top, one_mul]

theorem measurable_detNorm (E : Type) [Field E] [NumberField E] (j : ℕ) :
    Measurable (detNorm E j) := by
  have hc : Continuous (fun x : InfinitePlace E → Fin j → Fin j → ℂ =>
      ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2) := by
    refine continuous_finsetProd _ (fun w _ => ?_)
    exact ((Continuous.matrix_det
      (A := fun x : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (x w)) (continuous_apply w)).norm).pow 2
  exact hc.measurable

theorem ae_detNorm_pos (E : Type) [Field E] [NumberField E] (j : ℕ) (hj : 1 ≤ j) :
    ∀ᵐ g ∂(haarGL E j), 0 < detNorm E j g := by
  have hm := GlobalTheory.FlagBase.MeanCov.measurable_detNorm E j
  rw [ae_iff]
  have hs : MeasurableSet {g : MatInf E j | ¬ 0 < detNorm E j g} :=
    (measurableSet_lt measurable_const hm).compl
  have hz : ∀ g ∈ {g : MatInf E j | ¬ 0 < detNorm E j g},
      ENNReal.ofReal ((detNorm E j g)⁻¹ ^ j) = 0 := by
    intro g hg
    have hnn : 0 ≤ detNorm E j g := by
      unfold detNorm
      exact Finset.prod_nonneg fun w _ => by positivity
    have h0 : detNorm E j g = 0 := le_antisymm (not_lt.mp hg) hnn
    rw [h0, _root_.inv_zero, zero_pow (by omega), ENNReal.ofReal_zero]
  unfold haarGL
  refine (withDensity_apply _ hs).trans ?_
  refine (setLIntegral_congr_fun hs hz).trans ?_
  simp

private theorem covol_covAt (E : Type) [Field E] [NumberField E] (hE : IsTotallyComplex E)
    (j : ℕ) (hj : 1 ≤ j) (w : ℝ → ENNReal) (hw : Measurable w)
    (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsFullLattice E Λ) :
    covol (autGL E j Λ) ((haarGL E j).withDensity fun g => w (covAt E j (latAt E j Λ g)))
        {g | 0 < detNorm E j g} =
      slabVol E j Λ * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal t := by
  obtain ⟨κ, hκ, hL⟩ :=
    (_root_.GlobalTheory.LatFacts.lattice_facts E hE j).1 Λ hΛ
  have hF : Measurable fun t : ℝ => w (κ / t) := hw.comp (measurable_const.div measurable_id)
  have hd : (haarGL E j).withDensity (fun g => w (covAt E j (latAt E j Λ g)))
      = (haarGL E j).withDensity (fun g => w (κ / detNorm E j g)) := by
    refine withDensity_congr_ae ?_
    filter_upwards [GlobalTheory.FlagBase.MeanCov.ae_detNorm_pos E j hj] with g hg
    rw [(hL g hg).2.1]
  rw [hd]
  refine (GlobalTheory.T.leftQuotientCovolume_withDensity_detNormSq E hE j hj _ hΛ
    (fun t => w (κ / t)) hF).trans ?_
  congr 1
  exact GlobalTheory.FlagBase.MeanCov.lintegral_div_inv κ hκ w

theorem latMean_covAt : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j → ∀ w : ℝ → ENNReal, Measurable w → latMean E j (fun L => w (covAt E j L)) = glVol E j * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal t := by
  intro E _ _ hE j hj w hw
  unfold latMean glVol
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun c => ?_
  obtain ⟨Λ, hΛ⟩ := c.out
  exact covol_covAt E hE j hj w hw Λ hΛ

end GlobalTheory.FlagBase.MeanCov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHsNormSqDoubleCosetLeFatou
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.FatouI

theorem lintegral_le_of_liminf {X : Type*} [MeasurableSpace X] (ν : Measure X) (F : X → ENNReal)
    (g : ℕ → X → ENNReal) (hg : ∀ j, Measurable (g j))
    (hF : ∀ᵐ γ ∂ν, F γ ≤ Filter.liminf (fun j => g j γ) Filter.atTop) (b : ℕ → ℝ) (L : ℝ)
    (hb : ∀ j, ∫⁻ γ, g j γ ∂ν = ENNReal.ofReal (b j))
    (hL : Filter.Tendsto b Filter.atTop (nhds L)) : ∫⁻ γ, F γ ∂ν ≤ ENNReal.ofReal L := by
  refine (lintegral_mono_ae hF).trans ((lintegral_liminf_le hg).trans ?_)
  simp_rw [hb]
  exact (ENNReal.tendsto_ofReal hL).liminf_eq.le

variable {k r : ℕ}

theorem measurable_besselTwoSidedAction_joint :
    Measurable fun q : Mt k r × (Mt k r × Mt k r) => act2 (Matrix.of q.1) q.2 := by
  let m : Mt k r × Mt k r → Mt k r := fun q => lmulM (Matrix.of q.1) q.2
  have hmul : Continuous m :=
    Continuous.matrix_mul (X := Mt k r × Mt k r) continuous_fst continuous_snd
  have hm : Measurable m := hmul.measurable
  have h1 : Measurable fun q : Mt k r × (Mt k r × Mt k r) => m (q.2.1, q.1) :=
    hm.comp (measurable_snd.fst.prodMk measurable_fst)
  have h2 : Measurable fun q : Mt k r × (Mt k r × Mt k r) => invM q.2.2 :=
    measurable_invM.comp measurable_snd.snd
  have h3 : Measurable fun q : Mt k r × (Mt k r × Mt k r) => m (m (q.2.1, q.1), invM q.2.2) :=
    hm.comp (h1.prodMk h2)
  exact h3

theorem hsNormSq_eq_sum {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem DD_stable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (hσ : IsURepOn (GG k r) σ) (hG : IsClosedSub k r (GG k r)) :
    ∀ g ∈ GG k r, ∀ v ∈ (DD σ w : Set H), σ g v ∈ (DD σ w : Set H) := by
  intro g hg v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨h, hh, rfl⟩ := hv
    have := mem_DD σ w (hG.2.2.2.1 g hg h hh)
    rw [hσ.1.2 g hg h hh] at this
    exact this
  | zero => simp
  | add u v _ _ hu hv => rw [map_add (f := _)]; exact (DD σ w).add_mem hu hv
  | smul a v _ hv => rw [map_smul]; exact (DD σ w).smul_mem a hv

theorem integrable_coef {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (hσ : IsURepOn (GG k r) σ) {S : Set (Mat k r)} (hS : IsClosedSub k r S)
    {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ) {a C : ℝ} (hfin : normInt μ a < ⊤) (u v : H)
    (hC : ∀ g ∈ GG k r, ‖coef σ u v g‖ ≤ C * opn g ^ (-a)) :
    Integrable (fun p : Mt k r => coef σ u v (Matrix.of p)) μ := by
  have hae : ∀ᵐ p ∂μ, (Matrix.of p : Mat k r) ∈ S := hμ.2.2.1
  have hSm : MeasurableSet {p : Mt k r | (Matrix.of p : Mat k r) ∈ S} :=
    IsClosed.measurableSet (α := Mt k r) hS.2.1
  refine ⟨?_, ?_⟩
  · have hc : ContinuousOn (fun p : Mt k r => coef σ u v (Matrix.of p))
        {p : Mt k r | (Matrix.of p : Mat k r) ∈ S} :=
      ContinuousOn.inner (𝕜 := ℂ) continuousOn_const ((hσ.2.2 u).mono hS.1)
    have := hc.aestronglyMeasurable (μ := μ) hSm
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {p : Mt k r | (Matrix.of p : Mat k r) ∈ S}) hae] at this
  · refine lt_of_le_of_lt (b := ∫⁻ x, ENNReal.ofReal C * ENNReal.ofReal (opn (Matrix.of x) ^ (-a)) ∂μ)
      (lintegral_mono_ae ?_) ?_
    · filter_upwards [hae] with p hp
      rw [← ENNReal.ofReal_mul' (Real.rpow_nonneg (opn_nonneg _) _), ← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hC _ (hS.1 hp))
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem dis_of_continuousOn {Ω S S' : Set (Mat k r)} {μG μS μS' ν : Measure (Mt k r)}
    (hG : IsClosedSub k r (GG k r)) (hS : IsClosedSub k r S) (hS' : IsClosedSub k r S')
    (hμG : IsHaarOn (GG k r) μG) (hμ : IsHaarOn S μS) (hμ' : IsHaarOn S' μS') (hΩ : Ω ⊆ GG k r)
    (hν : IsDis Ω μG μS μS' ν) (f : Mat k r → ℝ) (hf0 : ∀ g, 0 ≤ f g) (hf : ContinuousOn f (GG k r))
    (hfi : Integrable (fun g : Mt k r => f (Matrix.of g)) μG) :
    ∃ g : Mt k r → ENNReal, Measurable g ∧
      (∀ γ : Mt k r, Matrix.of γ ∈ Ω →
        g γ = ∫⁻ p, ENNReal.ofReal (f (Matrix.of (act2 (Matrix.of γ) p))) ∂(μS.prod μS')) ∧
      ∫⁻ γ, g γ ∂ν = ENNReal.ofReal (∫ g, f (Matrix.of g) ∂μG) := by
  classical
  haveI := hμ.1
  haveI := hμ'.1
  have hGm : MeasurableSet {p : Mt k r | (Matrix.of p : Mat k r) ∈ GG k r} :=
    IsClosed.measurableSet (α := Mt k r) hG.2.1
  let f0 : Mt k r → ℝ := {p : Mt k r | (Matrix.of p : Mat k r) ∈ GG k r}.piecewise
    (fun p => f (Matrix.of p)) (fun _ => 0)
  have hf0m : Measurable f0 :=
    ContinuousOn.measurable_piecewise (f := fun p : Mt k r => f (Matrix.of p)) hf continuousOn_const hGm
  have hf0e : ∀ p : Mt k r, Matrix.of p ∈ GG k r → f0 p = f (Matrix.of p) := fun p hp =>
    Set.piecewise_eq_of_mem _ _ _ hp
  have hF : Measurable fun p => ENNReal.ofReal (f0 p) := hf0m.ennreal_ofReal
  refine ⟨fun γ => ∫⁻ p, ENNReal.ofReal (f0 (act2 (Matrix.of γ) p)) ∂(μS.prod μS'), ?_, ?_, ?_⟩
  · exact (hF.comp measurable_besselTwoSidedAction_joint).lintegral_prod_right'
  · intro γ hγ
    have h1 : ∀ᵐ p ∂μS, (Matrix.of p : Mat k r) ∈ S := hμ.2.2.1
    have h2 : ∀ᵐ p ∂μS', (Matrix.of p : Mat k r) ∈ S' := hμ'.2.2.1
    have h1' := Measure.quasiMeasurePreserving_fst (μ := μS) (ν := μS') |>.ae h1
    have h2' := Measure.quasiMeasurePreserving_snd (μ := μS) (ν := μS') |>.ae h2
    refine lintegral_congr_ae ?_
    filter_upwards [h1', h2'] with p hp hp'
    rw [hf0e]
    exact hG.2.2.2.1 _ (hG.2.2.2.1 _ (hS.1 hp) _ (hΩ hγ)) _ (hG.2.2.2.2 _ (hS'.1 hp'))
  · rw [← hν.2.2 _ hF, ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall fun g => hf0 _)]
    have h1 : ∀ᵐ p ∂μG, (Matrix.of p : Mat k r) ∈ GG k r := hμG.2.2.1
    refine lintegral_congr_ae ?_
    filter_upwards [h1] with p hp
    rw [hf0e p hp]

end GlobalTheory.SgInf.FatouI


open GlobalTheory.SgInf.FatouI in
theorem GlobalTheory.SgInf.lintegral_hsNormSq_Iint_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ ν : Measure (Mt k r), IsDis (Greg k r z z') μG μS μS' ν → ∀ x ∈ DD σ w, ∀ y ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), ∫⁻ γ, ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ x y ξ ξ' (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal (d⁻¹ * (⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ).re * (⟪ξ', be (psiGen k r z' c') π' μS' σ x x ξ'⟫_ℂ).re) := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hSd hSd' ν hν x hx y hy ξ ξ'
  obtain ⟨hG, -, -, hS, -⟩ := _root_.GlobalTheory.SgInf.closedSub_groups k r z hSd.1 hSd.2.1
  obtain ⟨-, -, -, hS', -⟩ := _root_.GlobalTheory.SgInf.closedSub_groups k r z' hSd'.1 hSd'.2.1
  obtain ⟨Om, hOm⟩ := _root_.GlobalTheory.SgInf.FolnerSets.exists_isFolner k r z μS hSd.1 hSd.2.1 hSd.2.2.2.1
  obtain ⟨Om', hOm'⟩ := _root_.GlobalTheory.SgInf.FolnerSets.exists_isFolner k r z' μS' hSd'.1 hSd'.2.1 hSd'.2.2.2.1
  have hdec := hStd.2.2.2.2.2.2.2.1
  have ha : 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < a := by
    have h1 : (2 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
      have := hStd.1
      exact_mod_cast (by omega : 2 ≤ 2 * r + k + 1)
    have h2 : ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < ((2 * r + k + 1 : ℕ) : ℝ) ^ 5 :=
      pow_lt_pow_right₀ (by linarith) (by norm_num)
    have := hStd.2.2.2.2.2.2.1
    linarith
  have hiy : Integrable (fun p : Mt k r => coef σ y y (Matrix.of p)) μS := by
    obtain ⟨C, hC⟩ := hdec y hy y hy
    exact integrable_coef σ hStd.2.1 hS hSd.2.2.2.1 (_root_.GlobalTheory.SgGrowth.normInt_lt_top k r _ μS a hS hSd.2.2.2.1 ha) y y hC
  have hix : Integrable (fun p : Mt k r => coef σ x x (Matrix.of p)) μS' := by
    obtain ⟨C, hC⟩ := hdec x hx x hx
    exact integrable_coef σ hStd.2.1 hS' hSd'.2.2.2.1 (_root_.GlobalTheory.SgGrowth.normInt_lt_top k r _ μS' a hS' hSd'.2.2.2.1 ha) x x hC
  have h62 := fun j => _root_.GlobalTheory.SgInf.TruncNorm.truncated_norm_sq k r σ w a μG d z c π μS z' c' π' μS' hStd hSd hSd' x y ξ ξ' (Om j) (Om' j)
    (hOm.1 j).1 (hOm'.1 j).1 (hOm.1 j).2.2.2.2 (hOm'.1 j).2.2.2.2 hiy hix
  have h63 := _root_.GlobalTheory.SgInf.FolnerLimit.folner_limit k r σ w a μG d z c π μS hStd hSd Om hOm y hy ξ
  have h63' := _root_.GlobalTheory.SgInf.FolnerLimit.folner_limit k r σ w a μG d z' c' π' μS' hStd hSd' Om' hOm' x hx ξ'
  have h64 := _root_.GlobalTheory.SgInf.FolnerLower.hsNormSq_Iint_le_liminf k r σ w a μG d z c π μS z' c' π' μS' hStd hSd hSd' Om Om' hOm hOm' x hx y hy ξ ξ'
  have hadj := (_root_.GlobalTheory.SgInf.BeForm.be_converges_equivariant_hermitian_continuous k r σ w a μG d z c π μS hStd hSd (DD σ w) (DD_stable σ w hStd.2.1 hG) hdec
    y hy y hy).2.2.1
  have him : (⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ).im = 0 := by
    rw [← Complex.conj_eq_iff_im, inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right, hadj]
  have hcont : Continuous (hsNormSq : (Wq →L[ℂ] Wp) → ℝ) := by
    have : (hsNormSq : (Wq →L[ℂ] Wp) → ℝ) = fun A => ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 :=
      funext hsNormSq_eq_sum
    rw [this]
    fun_prop
  have hnn : ∀ A : Wq →L[ℂ] Wp, 0 ≤ hsNormSq A := fun A => by
    rw [hsNormSq_eq_sum]; positivity
  have hdis := fun j => dis_of_continuousOn hG hS hS' hStd.2.2.2.2.1 hSd.2.2.2.1 hSd'.2.2.2.1
    (Greg_subset z z') hν (fun g => hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π'
      (μS.restrict (Om j)) (μS'.restrict (Om' j)) σ x y ξ ξ' g)) (fun g => hnn _)
      (hcont.comp_continuousOn (h62 j).1) (h62 j).2.1
  choose g hgm hge hgi using hdis
  have hpos : ∀ j, 0 < (μS (Om j)).toReal := fun j =>
    ENNReal.toReal_pos (hOm.1 j).2.2.2.1.ne' (hOm.1 j).2.2.2.2.ne
  have hpos' : ∀ j, 0 < (μS' (Om' j)).toReal := fun j =>
    ENNReal.toReal_pos (hOm'.1 j).2.2.2.1.ne' (hOm'.1 j).2.2.2.2.ne
  refine lintegral_le_of_liminf ν _ (fun j γ => g j γ / (μS (Om j) * μS' (Om' j)))
    (fun j => (hgm j).div_const _) ?_
    (fun j => (∫ g, hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π'
      (μS.restrict (Om j)) (μS'.restrict (Om' j)) σ x y ξ ξ' (Matrix.of g)) ∂μG) /
        ((μS (Om j)).toReal * (μS' (Om' j)).toReal)) _ ?_ ?_
  · have h1 : ∀ᵐ γ ∂ν, (Matrix.of γ : Mat k r) ∈ Greg k r z z' := hν.2.1
    filter_upwards [h1] with γ hγ
    simp_rw [fun j => hge j γ hγ]
    exact h64 _ hγ
  · intro j
    simp_rw [div_eq_mul_inv (g j _)]
    rw [lintegral_mul_const _ (hgm j), hgi j, ENNReal.ofReal_div_of_pos (mul_pos (hpos j) (hpos' j)),
      ENNReal.ofReal_mul (hpos j).le, ENNReal.ofReal_toReal (hOm.1 j).2.2.2.2.ne,
      ENNReal.ofReal_toReal (hOm'.1 j).2.2.2.2.ne, div_eq_mul_inv]
  · have hT := (Complex.continuous_re.tendsto _).comp ((h63.const_mul ((d : ℂ)⁻¹)).mul h63')
    convert hT using 2 with j
    · have e := (h62 j).2.2
      rw [Function.comp_apply, ← mul_div_assoc (d : ℂ)⁻¹, div_mul_div_comm, ← e]
      norm_cast
    · rw [← Complex.ofReal_inv, mul_assoc (_ : ℂ), Complex.re_ofReal_mul, Complex.mul_re, him]
      ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemCongruenceLevelIffOrthEmbeddingStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_congruence_level_iff_orthEmbedding : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ jf : D.inst.Gf →* I.Gf, IsFinEmb D x A jf → (∀ g, g ∈ D.inst.Kset ↔ xf⁻¹ * jf g * xf ∈ I.Kset) ∧ ∀ (N : ℕ) (g : D.inst.Gf), g ∈ D.inst.Kg N ↔ xf⁻¹ * jf g * xf ∈ I.Kg N := by
  first | exact @GlobalTheory.StabUnfold.mem_level_iff_of_isFinEmb | exact GlobalTheory.StabUnfold.mem_level_iff_of_isFinEmb | (intros; apply GlobalTheory.StabUnfold.mem_level_iff_of_isFinEmb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeFrameEqStandardTranslate
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.StdLat

theorem eq_img_lamStd : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∃ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L ∧ (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f ∧ ∃ n ∈ Fr.N, (∀ b, n (Fr.f b) = Fr.f b) ∧ Λ = img n (Fr.LamStd L) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r Fr Λ hSD hFr
  obtain ⟨y, hyΛ, hyf⟩ := _root_.GlobalTheory.SelfDualFrame.exists_dual_family M hM H r Fr Λ hSD hFr
  have hy0 : ∀ (a : Fin r) (b : Fin (r + 1)), H.h (y a.castSucc) (Fr.f b) = if b = a.castSucc then 1 else 0 :=
    fun a b => hyf b a.castSucc
  obtain ⟨y', hy'Λ, hy'f, hy'y⟩ := _root_.GlobalTheory.IsotropicDual.isotropic_dual M hM H r Fr Λ hSD hFr (fun a : Fin r => y a.castSucc) (fun a : Fin r => hyΛ _) hy0
  obtain ⟨n, hnU, hnf, hnes, hnX⟩ := _root_.GlobalTheory.UnipFrame.exists_unitary_frame_dual M H r Fr y' hy'f hy'y
  obtain ⟨L, hLset, hLin⟩ := _root_.GlobalTheory.StdLatInner.exists_inner M hM H r Fr Λ hSD hFr y' hy'Λ hy'f
  have heΛ : ∀ a : Fin r, Fr.f a.castSucc ∈ Λ := fun a => hFr.1.1 _
  refine ⟨L, hLin, hLset, n, ?_, hnf, ?_⟩
  · apply Subgroup.subset_closure
    refine ⟨hnU, ?_, hnX⟩
    intro j _ v hv
    have hle : Fr.Fj j ≤ LinearMap.ker ((n : V →ₗ[E] V) - LinearMap.id) := by
      rw [FrameD.Fj, Submodule.span_le]
      rintro _ ⟨a, _, rfl⟩
      simp [FrameD.e, hnf]
    have h1 := hle hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at h1
    rw [show n v - v = 0 from h1]
    exact zero_mem _
  · exact _root_.GlobalTheory.StdLatImg.eq_img_lamStd M H r Fr Λ hSD heΛ L hLset n hnU (fun a => hnf _) (fun a => by rw [hnes]; exact hy'Λ a) hnX

end GlobalTheory.StdLat
end

