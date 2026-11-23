module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0207
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankTwoDefiniteUnimodularHermitianClassBound
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityDetNormSq
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.DetSlab

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

theorem detNorm_mul (x y : MatInf E j) : detNorm E j (x * y) = detNorm E j x * detNorm E j y := by
  unfold detNorm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : Matrix.of ((x * y) w) = Matrix.of (x w) * Matrix.of (y w) := rfl
  rw [this, Matrix.det_mul, norm_mul, mul_pow]

theorem detNorm_nonneg (x : MatInf E j) : 0 ≤ detNorm E j x :=
  Finset.prod_nonneg fun _ _ => sq_nonneg _

theorem detNorm_aut (hE : IsTotallyComplex E) (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsFullLattice E Λ)
    {x : MatInf E j} (hx : x ∈ autGL E j Λ) : detNorm E j x = 1 := by
  obtain ⟨γ, hγ, hx⟩ := hx
  have h1 : IsIntegral ℤ (γ : Matrix (Fin j) (Fin j) E).det :=
    GlobalTheory.Mem.StabDet.isIntegral_det Λ hΛ.fg (Submodule.IsFullLattice.span_eq_top (self := hΛ)) _ fun v hv => (hγ v).2 hv
  have h2 : IsIntegral ℤ ((γ⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E).det :=
    GlobalTheory.Mem.StabDet.isIntegral_det Λ hΛ.fg (Submodule.IsFullLattice.span_eq_top (self := hΛ)) _ fun v hv => (hγ _).1 (by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact hv)
  have h3 : (γ : Matrix (Fin j) (Fin j) E).det * ((γ⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  let u : (𝓞 E)ˣ := Units.mkOfMulEqOne ⟨_, h1⟩ ⟨_, h2⟩ (RingOfIntegers.ext h3)
  have h4 := InfinitePlace.prod_eq_abs_norm ((u : 𝓞 E) : E)
  rw [NumberField.Units.norm] at h4
  have hu : ((u : 𝓞 E) : E) = (γ : Matrix (Fin j) (Fin j) E).det := rfl
  rw [hu] at h4
  unfold detNorm
  rw [Rat.cast_one] at h4
  rw [← h4]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h5 : Matrix.of (x w) = w.embedding.mapMatrix (γ : Matrix (Fin j) (Fin j) E) := by
    ext a b
    simpa using hx w a b
  rw [h5, ← RingHom.map_det, InfinitePlace.norm_embedding_eq, (IsTotallyComplex.isComplex w).mult_eq_two]

theorem continuous_detNorm :
    Continuous (fun x : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j x) := by
  unfold detNorm
  refine continuous_finsetProd _ fun w _ => ?_
  exact (Continuous.matrix_det (continuous_apply w)).norm.pow 2

theorem measurable_detNorm : Measurable (detNorm E j) := (continuous_detNorm E j).measurable

def scal (t : ℝ) (x : MatInf E j) : MatInf E j := fun w a b => (t : ℂ) * x w a b

theorem measurable_scal (t : ℝ) : Measurable (scal E j t) :=
  (continuous_const_smul t : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => t • x).measurable

theorem detNorm_scal (t : ℝ) (x : MatInf E j) :
    detNorm E j (scal E j t x) = |t| ^ (2 * j * Fintype.card (InfinitePlace E)) * detNorm E j x := by
  unfold detNorm
  have : ∀ w, Matrix.of (scal E j t x w) = (t : ℂ) • Matrix.of (x w) := fun w => rfl
  simp only [this, Matrix.det_smul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_const, Fintype.card_fin, Finset.card_univ, ← pow_mul]
  rw [mul_comm j 2]

theorem isAddHaar_volume : (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).IsAddHaarMeasure := by
  haveI h1 : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI h2 : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

theorem lintegral_scal (t : ℝ) (ht : t ≠ 0) (f : MatInf E j → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f (scal E j t x) ∂(haarGL E j) = ∫⁻ x, f x ∂(haarGL E j) := by
  have hd : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
    (((measurable_detNorm E j).inv).pow_const j).ennreal_ofReal
  have hf' : Measurable (fun x : InfinitePlace E → Fin j → Fin j → ℂ => f x) := hf
  have hf'' : Measurable (fun x : InfinitePlace E → Fin j → Fin j → ℂ => f (t • x)) :=
    hf.comp (measurable_scal E j t)
  have e1 := lintegral_withDensity_eq_lintegral_mul (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) hd hf'
  have e2 := lintegral_withDensity_eq_lintegral_mul (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) hd hf''
  refine e2.trans (Eq.trans ?_ e1.symm)
  haveI := isAddHaar_volume E j
  have hm := Measure.map_addHaar_smul (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) ht
  have hrk : Module.finrank ℝ (InfinitePlace E → Fin j → Fin j → ℂ) =
      2 * j * Fintype.card (InfinitePlace E) * j := by
    simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    ring
  have e3 := lintegral_map (μ := (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))) (hd.mul hf')
    (measurable_const_smul t)
  rw [hm, lintegral_smul_measure, hrk, smul_eq_mul] at e3
  set N := 2 * j * Fintype.card (InfinitePlace E) with hN
  have hpos : 0 < |t| ^ (N * j) := pow_pos (abs_pos.2 ht) _
  have e4 : ∀ x : InfinitePlace E → Fin j → Fin j → ℂ, ENNReal.ofReal ((detNorm E j (t • x))⁻¹ ^ j) =
      ENNReal.ofReal |(t ^ (N * j))⁻¹| * ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) := by
    intro x
    have h : detNorm E j (t • x) = |t| ^ N * detNorm E j x := detNorm_scal E j t x
    rw [← ENNReal.ofReal_mul (abs_nonneg _), h, abs_inv, abs_pow, mul_inv, mul_pow,
      inv_pow, ← pow_mul]
  have e5 := lintegral_const_mul (μ := (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)))
    (ENNReal.ofReal |(t ^ (N * j))⁻¹|) (hd.mul hf'')
  replace e3 := e3.trans ((lintegral_congr fun x => (congrArg (· * f (scal E j t x)) (e4 x)).trans
    (mul_assoc _ _ _)).trans e5)
  have hne : ENNReal.ofReal |(t ^ (N * j))⁻¹| ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le, abs_inv, abs_pow]; exact inv_pos.2 hpos
  exact ((ENNReal.mul_right_inj hne ENNReal.ofReal_ne_top).1 e3).symm

theorem restrict_pos (hj : 1 ≤ j) : (haarGL E j).restrict {g | 0 < detNorm E j g} = haarGL E j := by
  refine Measure.restrict_eq_self_of_ae_mem ?_
  have hd : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
    (((measurable_detNorm E j).inv).pow_const j).ennreal_ofReal
  refine (ae_withDensity_iff hd).2 (Filter.Eventually.of_forall fun x hx => ?_)
  refine lt_of_le_of_ne (detNorm_nonneg E j x) fun h => hx ?_
  rw [← h, _root_.inv_zero, zero_pow (by omega), ENNReal.ofReal_zero]

theorem sFinite_haarGL : SFinite (haarGL E j) := by
  haveI := isAddHaar_volume E j
  exact (Measure.withDensity.instSFinite :
    SFinite (Measure.withDensity (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) _))

theorem lintegral_exp (F : ℝ → ENNReal) :
    ∫⁻ u, F (Real.exp u) = ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.univ) (f := Real.exp) (f' := Real.exp)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t => F t / ENNReal.ofReal t)
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [h]
  refine lintegral_congr fun u => ?_
  rw [abs_of_pos (Real.exp_pos u), ENNReal.mul_div_cancel
    (by simpa using Real.exp_pos u) ENNReal.ofReal_ne_top]

theorem lintegral_cone (hj : 1 ≤ j) (D : Set (MatInf E j)) (hD : MeasurableSet D)
    (hpos : D ⊆ {g | 0 < detNorm E j g}) (hsc : ∀ g ∈ D, ∀ t : ℝ, 0 < t → scal E j t g ∈ D)
    (F : ℝ → ENNReal) (hF : Measurable F) :
    ∫⁻ g in D, F (detNorm E j g) ∂(haarGL E j) =
      haarGL E j ({x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} ∩ D) *
        ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  haveI := sFinite_haarGL E j
  have hl : Measurable fun g => Real.log (detNorm E j g) := Real.measurable_log.comp (measurable_detNorm E j)
  set ν : Measure ℝ := ((haarGL E j).restrict D).map fun g => Real.log (detNorm E j g) with hν
  have hνa : ∀ s, MeasurableSet s → ν s = haarGL E j ((fun g => Real.log (detNorm E j g)) ⁻¹' s ∩ D) :=
    fun s hs => by rw [hν, Measure.map_apply hl hs, Measure.restrict_apply (hl hs)]
  set N := 2 * j * Fintype.card (InfinitePlace E) with hN
  have hN0 : (N : ℝ) ≠ 0 := by
    have : 0 < N := Nat.mul_pos (by omega) Fintype.card_pos
    exact_mod_cast this.ne'
  haveI : ν.IsAddLeftInvariant := by
    refine ⟨fun c => ?_⟩
    ext s hs
    have hc : Measurable fun u : ℝ => c + u := measurable_const_add c
    rw [Measure.map_apply hc hs, hνa _ (hc hs), hνa _ hs]
    have hA : MeasurableSet ((fun g => Real.log (detNorm E j g)) ⁻¹' s ∩ D) := (hl hs).inter hD
    have hB : MeasurableSet ((fun g => Real.log (detNorm E j g)) ⁻¹' ((fun u => c + u) ⁻¹' s) ∩ D) :=
      (hl (hc hs)).inter hD
    have ht : 0 < Real.exp (c / N) := Real.exp_pos _
    rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hB,
      ← lintegral_scal E j _ ht.ne' _ (measurable_one.indicator hA)]
    refine lintegral_congr fun x => ?_
    have hback : scal E j (Real.exp (c / N))⁻¹ (scal E j (Real.exp (c / N)) x) = x := by
      funext w a b
      simp only [scal]
      rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne', Complex.ofReal_one, one_mul]
    have hlog : x ∈ D → Real.log (detNorm E j (scal E j (Real.exp (c / N)) x)) =
        c + Real.log (detNorm E j x) := fun hx => by
      have h0 : 0 < detNorm E j x := hpos hx
      rw [detNorm_scal, abs_of_pos ht, Real.log_mul (pow_pos ht _).ne' h0.ne', Real.log_pow, Real.log_exp, ← hN,
        mul_div_cancel₀ _ hN0]
    refine (Set.indicator_const_eq_indicator_const (c := (1 : ENNReal)) ⟨fun h => ⟨?_, hsc _ h.2 _ ht⟩, fun h => ?_⟩)
    · have := h.1
      simp only [Set.mem_preimage] at this ⊢
      rwa [hlog h.2]
    · have hx : x ∈ D := hback ▸ hsc _ h.2 _ (inv_pos.2 ht)
      refine ⟨?_, hx⟩
      have := h.1
      simp only [Set.mem_preimage] at this ⊢
      rwa [hlog hx] at this
  have hv : (volume : Measure ℝ) (Set.Ico 0 1) = 1 := by simp
  have hFe : Measurable fun u => F (Real.exp u) := hF.comp Real.measurable_exp
  have h1 := measure_add_lintegral_eq volume ν (s := Set.Ico 0 1) measurableSet_Ico _ hFe
  simp only [measure_preimage_add_right] at h1
  rw [hv, one_mul, lintegral_const_mul _ (f := fun u => F (Real.exp (-u))) (hFe.comp measurable_neg), lintegral_neg_eq_self (fun u => F (Real.exp u)),
    hνa _ measurableSet_Ico] at h1
  have hset : (fun g => Real.log (detNorm E j g)) ⁻¹' Set.Ico 0 1 ∩ D =
      {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} ∩ D := by
    ext x
    refine and_congr_left fun hx => ?_
    have h0 : 0 < detNorm E j x := hpos hx
    simp only [Set.mem_preimage, Set.mem_Ico, Set.mem_setOf_eq]
    rw [Real.log_nonneg_iff h0, Real.log_lt_iff_lt_exp h0]
  rw [hset] at h1
  have h2 : ∫⁻ u, F (Real.exp u) ∂ν = ∫⁻ g in D, F (detNorm E j g) ∂(haarGL E j) := by
    rw [hν, lintegral_map hFe hl]
    refine setLIntegral_congr_fun hD fun x hx => ?_
    simp only [Real.exp_log (hpos hx)]
  rw [← h2, h1, lintegral_exp]

theorem covol_withDensity_detNorm : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ), 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → ∀ F : ℝ → ENNReal, Measurable F → covol (autGL E j Λ) ((haarGL E j).withDensity fun x => F (detNorm E j x)) {x | 0 < detNorm E j x} = covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} * ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  intro E _ _ hE j hj Λ hΛ F hF
  obtain ⟨D, hD, hpos, -, hsc, hcov⟩ :=
    GlobalTheory.T.exists_scalarStable_latticeAutomorphismFundamentalDomain E hE j Λ hΛ
  have hm := measurable_detNorm E j
  have hP : MeasurableSet {g : MatInf E j | 0 < detNorm E j g} := measurableSet_lt measurable_const hm
  have hS : MeasurableSet {x : MatInf E j | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} :=
    (measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)
  have hinv : ∀ γ ∈ autGL E j Λ, ∀ g, detNorm E j (γ * g) = detNorm E j g := fun γ hγ g => by
    rw [detNorm_mul, detNorm_aut E j hE Λ hΛ hγ, one_mul]
  have h1 := hcov (fun x => F (detNorm E j x)) _ ((hF.comp hm).indicator hP)
    (fun γ hγ g _ => by simp only [hinv γ hγ g]) hP subset_rfl
    (fun γ hγ g hg => by simpa only [Set.mem_setOf_eq, hinv γ hγ g] using hg)
  have h2 := hcov (fun _ => 1) _ (measurable_const.indicator hP) (fun _ _ _ _ => rfl) hS
    (fun g hg => lt_of_lt_of_le one_pos hg.1)
    (fun γ hγ g hg => by simpa only [Set.mem_setOf_eq, hinv γ hγ g] using hg)
  rw [restrict_pos E j hj] at h1 h2
  rw [withDensity_const, one_smul, setLIntegral_one] at h2
  rw [h1, h2, Set.inter_eq_right.2 hpos]
  exact lintegral_cone E j hj D hD hpos hsc F hF

end GlobalTheory.DetSlab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableTranslatedLatticeFunctionsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_translatedLattice_functions : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, ∀ (w : ℝ → ENNReal) (Φ : VecInf E j → ENNReal), Measurable w → Measurable Φ → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => w (covAt E j (latAt E j Λ g))) g) ∧ Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => ∑' x : {x : VecInf E j // x ∈ latAt E j Λ g ∧ x ≠ 0}, Φ x.1) g) ∧ Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => ∑' x : {x : VecInf E j // x ∈ dualAt E j (latAt E j Λ g) ∧ x ≠ 0}, Φ x.1) g) := by
  first
  | exact @GlobalTheory.LatMeasurable.measurable_latFun
  | intro E _ _ hE j w Φ hw hΦ Λ hΛ
    exact GlobalTheory.LatMeasurable.measurable_latFun E hE j w Φ hw hΦ Λ hΛ.toIsLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingRearrangePiProdMeasuresStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePreserving_rearrange_pi_prod_measures : ∀ (V V' V'' : Type) [Fintype V] [Fintype V'] [Fintype V''] (β : V ≃ V') (σ : V ≃ V'') (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (Y : V'' → Type) [∀ w, MeasurableSpace (Y w)] (m : ∀ i, Measure (X i)) [∀ i, SigmaFinite (m i)] (ν : ∀ w, Measure (Y w)) [∀ w, SigmaFinite (ν w)] (b : Fin a → ℝ) (c : V'' → ℝ), (∀ i, 0 ≤ b i) → (∀ w, 0 ≤ c w) → MeasurePreserving (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v))) (((∏ i, ENNReal.ofReal (b i ^ Fintype.card V)) * ENNReal.ofReal (∏ w, c w)) • (Measure.pi fun i => Measure.pi fun _ : V' => m i).prod (Measure.pi ν)) (Measure.pi fun v : V => (Measure.pi fun i => ENNReal.ofReal (b i) • m i).prod (ENNReal.ofReal (c (σ v)) • ν (σ v))) := by
  first | exact @GlobalTheory.LeviIso.measurePreserving_rearrange | exact GlobalTheory.LeviIso.measurePreserving_rearrange | (intros; apply GlobalTheory.LeviIso.measurePreserving_rearrange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MultipliableOfRealReOfComplex
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory

theorem multipliable_ofReal_re_of_complex (ι : Type) (c : ι → ℂ) (hc : Multipliable c)
    (hcr : ∀ i, (c i).im = 0 ∧ 0 ≤ (c i).re) :
    Multipliable (fun i => ENNReal.ofReal (c i).re) ∧
      ∏' i, ENNReal.ofReal (c i).re = ENNReal.ofReal (∏' i, c i).re := by
  obtain ⟨a, ha⟩ := hc
  have hc' : ∀ i, c i = ((c i).re : ℂ) := fun i => Complex.ext (by simp) (by simp [(hcr i).1])
  have hre : HasProd (fun i => (c i).re) a.re := by
    have h := (Complex.continuous_re.tendsto a).comp ha
    refine h.congr ?_
    intro s
    simp only [Function.comp]
    rw [Finset.prod_congr rfl (fun i _ => hc' i), ← Complex.ofReal_prod, Complex.ofReal_re]
  have h2 : HasProd (fun i => ENNReal.ofReal (c i).re) (ENNReal.ofReal a.re) := by
    have h := (ENNReal.continuous_ofReal.tendsto a.re).comp hre
    refine h.congr ?_
    intro s
    simp only [Function.comp]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (hcr i).2)]
  exact ⟨h2.multipliable, by rw [h2.tprod_eq, ha.tprod_eq]⟩

theorem multipliable_ofReal_re_of_complex' : ∀ (ι : Type) (c : ι → ℂ), Multipliable c → (∀ i, (c i).im = 0 ∧ 0 ≤ (c i).re) → Multipliable (fun i => ENNReal.ofReal (c i).re) ∧ ∏' i, ENNReal.ofReal (c i).re = ENNReal.ofReal (∏' i, c i).re :=
  multipliable_ofReal_re_of_complex

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairLatticeLeLiftedPairLatticeSupIsotropic
section
noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.PairLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' T₂ : E}
  {Λ : Submodule (𝓞 E) S.V} {g : ℕ}

theorem mem_orth {U : Submodule E S.V} {x : S.V} : x ∈ orth S U ↔ ∀ u ∈ U, S.hT u x = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem hT_z_X (F : LFlag S r T) {x : S.V} (hx : x ∈ Xsp F) : S.hT F.fl.z x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    have h := S.herm.eq (F.fl.e a) F.fl.z
    rw [F.fl.z_orth a] at h
    simpa using h.symm
  | zero => simp
  | add y z _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

theorem X_eq_Xflag (F : LFlag S r T) : Xsp F = Xflag F r := by
  change Submodule.span E (Set.range F.fl.e) = Submodule.span E (F.fl.e '' {i | i.1 < r})
  congr 1
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, rfl⟩
  · rintro ⟨a, _, rfl⟩
    exact ⟨a, rfl⟩

theorem mem_Lsub_of {F : LFlag S r T} {l y : S.V} (hl : l ∈ Lrep Λ F) (h : y - l ∈ Xsp F) :
    y ∈ Lsub Λ F := by
  have hlo : l ∈ orth S (Xsp F) := (Submodule.mem_inf.1 hl).2
  have hy : y = l + (y - l) := by abel
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [hy]
    exact Submodule.add_mem_sup hl h
  · rw [hy]
    exact (orth S (Xsp F)).add_mem hlo (FrEqv.X_le_orth h)

theorem IotaRel_zero (F : LFlag S r T) (F' : LFlag S r T') : IotaRel Λ g F F' 0 :=
  ⟨0, Submodule.zero_mem _, by simp, 0, Submodule.zero_mem _, by simp, by simp⟩

theorem IotaRel_add {F : LFlag S r T} {F' : LFlag S r T'} {x y : S.V}
    (hx : IotaRel Λ g F F' x) (hy : IotaRel Λ g F F' y) : IotaRel Λ g F F' (x + y) := by
  obtain ⟨l, hl, h1, l', hl', h2, h3⟩ := hx
  obtain ⟨m, hm, k1, m', hm', k2, k3⟩ := hy
  refine ⟨l + m, Submodule.add_mem _ hl hm, ?_, l' + m', Submodule.add_mem _ hl' hm', ?_, ?_⟩
  · have := (Xsp F).add_mem h1 k1
    rwa [show x - l + (y - m) = x + y - (l + m) by abel] at this
  · have := (Xsp F').add_mem h2 k2
    rwa [show x - l' + (y - m') = x + y - (l' + m') by abel] at this
  · have := Submodule.add_mem _ h3 k3
    rwa [show l - l' + (m - m') = l + m - (l' + m') by abel] at this

theorem IotaRel_smul {F : LFlag S r T} {F' : LFlag S r T'} {x : S.V} (o : 𝓞 E)
    (hx : IotaRel Λ g F F' x) : IotaRel Λ g F F' (o • x) := by
  obtain ⟨l, hl, h1, l', hl', h2, h3⟩ := hx
  refine ⟨o • l, Submodule.smul_mem _ o hl, ?_, o • l', Submodule.smul_mem _ o hl', ?_, ?_⟩
  · rw [← smul_sub]
    exact (toO S (Xsp F)).smul_mem o h1
  · rw [← smul_sub]
    exact (toO S (Xsp F')).smul_mem o h2
  · rw [← smul_sub]
    exact Submodule.smul_mem _ o h3

theorem La_props {F : LFlag S r T} {F' : LFlag S r T'} {x : S.V} (hx : x ∈ La Λ g F F') :
    x ∈ L0sub Λ F ∧ x ∈ L0sub Λ F' ∧ IotaRel Λ g F F' x := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx.2
  | zero => exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, IotaRel_zero F F'⟩
  | add y z _ _ h1 h2 =>
    exact ⟨Submodule.add_mem _ h1.1 h2.1, Submodule.add_mem _ h1.2.1 h2.2.1, IotaRel_add h1.2.2 h2.2.2⟩
  | smul c y _ h =>
    exact ⟨Submodule.smul_mem _ c h.1, Submodule.smul_mem _ c h.2.1, IotaRel_smul c h.2.2⟩

theorem map_Lrep {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V} (hβ : IsAutLam S Λ β)
    (hX : (Xsp F').map (β : S.V →ₗ[E] S.V) = Xsp F'') {l : S.V} (hl : l ∈ Lrep Λ F') :
    β l ∈ Lrep Λ F'' := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hl
  refine Submodule.mem_inf.2 ⟨(FrEqv.aut_mem_iff hβ l).2 h1, ?_⟩
  refine mem_orth.2 fun u hu => ?_
  rw [← hX] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  have := hβ.1 v l
  exact this.trans (mem_orth.1 h2 v hv)

theorem Mlat_le_La_sup (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E)
    (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hP : IsPair Λ F F' F'' β g) : Mlat Λ F F' F'' β g ≤ La Λ g F F'' ⊔ toO S (Xsp F) := by
  obtain ⟨hβ, hfl, hz, hc⟩ := hP
  have hX : (Xsp F').map (β : S.V →ₗ[E] S.V) = Xsp F'' := by
    rw [X_eq_Xflag F', X_eq_Xflag F'']
    exact hfl r
  intro x₁ hx
  obtain ⟨hLa, hTh⟩ := Submodule.mem_inf.1 hx
  obtain ⟨h0, h0', l, hl, hxl, l', hl', hxl', hll⟩ := La_props hLa
  have hz1 : S.hT F.fl.z x₁ = 0 := (Submodule.mem_inf.1 h0).2
  have hz1' : S.hT F'.fl.z x₁ = 0 := (Submodule.mem_inf.1 h0').2
  obtain ⟨⟨a, x₂⟩, hp, he⟩ := (Submodule.restrictScalars_mem _ _ _).1 hTh
  have hax : a = x₁ := he
  subst hax
  obtain ⟨⟨hprod, h12⟩, hβ12⟩ := Submodule.mem_inf.1 hp |>.imp_left Submodule.mem_inf.1
  have hx₂ : x₂ ∈ Hp Λ F F'' := hprod.2
  have h12 : a - x₂ ∈ Xsp F := h12
  have hβ12 : β a - x₂ ∈ Xsp F'' := hβ12
  have hβl : β l' ∈ Lrep Λ F'' := map_Lrep hβ hX hl'
  have hβd : β (a - l') ∈ Xsp F'' := by
    rw [← hX]
    exact ⟨a - l', hxl', rfl⟩
  have k1 : x₂ - l ∈ Xsp F := by
    have := (Xsp F).sub_mem hxl h12
    rwa [show a - l - (a - x₂) = x₂ - l by abel] at this
  have k2 : x₂ - β l' ∈ Xsp F'' := by
    have := (Xsp F'').sub_mem hβd hβ12
    rwa [map_sub, show β a - β l' - (β a - x₂) = x₂ - β l' by abel] at this
  have m1 : S.hT F.fl.z x₂ = 0 := by
    have := hT_z_X F h12
    rw [map_sub, hz1, zero_sub, neg_eq_zero] at this
    exact this
  have m2 : S.hT F''.fl.z x₂ = 0 := by
    have := hT_z_X F'' hβ12
    rw [map_sub, ← hz, hβ.1 F'.fl.z a, hz1', zero_sub, neg_eq_zero, hz] at this
    exact this
  have hmem : x₂ ∈ La Λ g F F'' := by
    refine Submodule.subset_span ⟨hx₂, Submodule.mem_inf.2 ⟨mem_Lsub_of hl k1, m1⟩,
      Submodule.mem_inf.2 ⟨mem_Lsub_of hβl k2, m2⟩, l, hl, k1, β l', hβl, k2, ?_⟩
    exact (hc l' hl' l hl).1 hll
  have hsum : a = x₂ + (a - x₂) := by abel
  rw [hsum]
  exact Submodule.add_mem_sup hmem h12

end GlobalTheory.LoopC.PairLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankTwoDefiniteUnimodularHermitianClassBoundStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_two_definite_unimodular_hermitian_class_bound : RankTwoClasses := by
  first | exact @GlobalTheory.RankTwoCount.rankTwoClasses | exact GlobalTheory.RankTwoCount.rankTwoClasses | (intros; apply GlobalTheory.RankTwoCount.rankTwoClasses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalBlockFrameLocalSplitStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_block_frame_local_split : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ) (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' → (∀ b, Submodule.IsFullLattice E (Λ b)) → (∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0)) → (∀ (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Biorth r m (fun b => P⁻¹ * (T b).map φ) (fun b => (T' b).map φ * P) ∧ ∀ k y, y ∈ locFlag φ P F k ↔ ∀ b, k ≤ b → ((T' b).map φ * P) *ᵥ y = 0) ∧ ∀ c, (∀ Y ∈ lowers F c, ∀ b, ∀ y ∈ Λ (b + c + 1), (T' b * Y * T (b + c + 1)) *ᵥ y ∈ Λ b) ∧ ∀ Z : ∀ b : Fin m, Matrix (Fin (r b)) (Fin (r (b + c + 1))) E, (∀ b : Fin m, ∀ y ∈ Λ (b + c + 1), Z b *ᵥ y ∈ Λ b) → ∃ Y ∈ lowers F c, ∀ b : Fin m, T' b * Y * T (b + c + 1) = Z b := by
  first
  | exact @GlobalTheory.RadCov.LocSplit.locSplit
  | intro E _ _ n m F r T T' Λ h hΛ hF
    exact GlobalTheory.RadCov.LocSplit.locSplit E n m F r T T' Λ h
      (fun b => (hΛ b).toIsLattice) hF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealComplexSpanOrthonormalSkewFamilyStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_complex_span_orthonormal_skew_family : ∀ (n d : ℕ) (ε : Fin n → Bool) (B : Fin d → Matrix (Fin n) (Fin n) ℂ) (s : Set (Fin d)), (∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0) → (∀ i, Formalism.REAL.inG ε (B i)) → (∀ X, (X ∈ Submodule.span ℂ (B '' s) ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (B '' s)) ∧ (∀ X ∈ Submodule.span ℂ (B '' s), ∀ i, i ∉ s → (X * (B i)ᴴ).trace = 0) ∧ ∀ X i, (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * (B i)ᴴ).trace = - starRingEnd ℂ (X * (B i)ᴴ).trace := by
  first | exact @GlobalTheory.SkewSpan.real_span | exact GlobalTheory.SkewSpan.real_span | (intros; apply GlobalTheory.SkewSpan.real_span <;> assumption)
end

