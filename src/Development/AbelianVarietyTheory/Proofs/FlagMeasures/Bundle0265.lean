module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LatExistsOfSteps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084
public import Formalism.LocalRingCardinality.DataSpaces
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0106
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0004
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0027
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasis
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRiemannianHaarUnitaryJSubgroupOfAlgebra
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open Filter Topology Metric Formalism.REAL

noncomputable section

namespace GlobalTheory.GaugeSubExists

open GlobalTheory.GaugeConst

variable {n : ℕ}

theorem exp_sub_one_mem (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ A) :
    NormedSpace.exp X - 1 ∈ A := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAddCommGroup
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X
  have h1 := (hasSum_nat_add_iff' 1).2 h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
    pow_zero, one_smul] at h1
  have hp : ∀ k : ℕ, X ^ (k + 1) ∈ A := by
    intro k
    induction k with
    | zero => simpa using hX
    | succ k ih => rw [pow_succ]; exact hA _ ih _ hX
  exact A.closed_of_finiteDimensional.mem_of_tendsto h1.tendsto_sum_nat
    (Eventually.of_forall fun m => A.sum_mem fun k _ => A.smul_mem _ (hp k))

def algSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : Subgroup (UJ ε) where
  carrier := {g | uMat g - 1 ∈ A}
  one_mem' := by
    change (1 : Matrix (Fin n) (Fin n) ℂ) - 1 ∈ A
    simp
  mul_mem' := by
    intro g h hg hh
    change uMat g * uMat h - 1 ∈ A
    have : uMat g * uMat h - 1 = (uMat g - 1) * (uMat h - 1) + (uMat g - 1) + (uMat h - 1) := by
      noncomm_ring
    rw [this]
    exact A.add_mem (A.add_mem (hA _ hg _ hh) hg) hh
  inv_mem' := by
    intro g hg
    have hgi : uMat g⁻¹ * uMat g = 1 := g.1.inv_mul
    have hst : ∀ x ∈ A, LinearMap.mulLeft ℝ (uMat g) x ∈ A := by
      intro x hx
      have : LinearMap.mulLeft ℝ (uMat g) x = (uMat g - 1) * x + x := by
        rw [LinearMap.mulLeft_apply]; noncomm_ring
      rw [this]
      exact A.add_mem (hA _ hg _ hx) hx
    have hinj : Function.Injective ((LinearMap.mulLeft ℝ (uMat g)).restrict hst) := by
      intro x y hxy
      have h1 : uMat g * x.1 = uMat g * y.1 := congrArg Subtype.val hxy
      have h2 := congrArg (uMat g⁻¹ * ·) h1
      simp only [← Matrix.mul_assoc, hgi, Matrix.one_mul] at h2
      exact Subtype.ext h2
    obtain ⟨x, hx⟩ := LinearMap.surjective_of_injective hinj ⟨_, hg⟩
    have h1 : uMat g * x.1 = uMat g - 1 := congrArg Subtype.val hx
    have h2 := congrArg (uMat g⁻¹ * ·) h1
    simp only [← Matrix.mul_assoc, hgi, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one] at h2
    change uMat g⁻¹ - 1 ∈ A
    rw [← neg_sub, ← h2]
    exact A.neg_mem x.2

theorem isClosed_algSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : IsClosed (algSub ε A hA : Set (UJ ε)) :=
  A.closed_of_finiteDimensional.preimage ((continuous_uMat ε).sub continuous_const)

theorem exists_preimage {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    (A : Submodule ℝ M) {f : M → M} (hf : HasStrictFDerivAt f (ContinuousLinearMap.id ℝ M) 0)
    (h0 : f 0 = 0) (hA : ∀ X ∈ A, f X ∈ A) {W : Set M} (hW : W ∈ 𝓝 (0 : M)) :
    ∀ᶠ a : A in 𝓝 0, ∃ Y ∈ A, Y ∈ W ∧ f Y = a.1 := by
  obtain ⟨p, hp⟩ := A.subtype.exists_leftInverse_of_injective A.ker_subtype
  have hp' : ∀ x : A, p x.1 = x := fun x => LinearMap.congr_fun hp x
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ _
  have h1 : HasStrictFDerivAt (fun x : A => f x.1) A.subtypeL 0 :=
    HasStrictFDerivAt.comp (0 : A) (g := f) (f := Subtype.val) hf A.subtypeL.hasStrictFDerivAt
  have h2 := (LinearMap.toContinuousLinearMap p).hasStrictFDerivAt.comp (0 : A) h1
  have h3 : (LinearMap.toContinuousLinearMap p).comp A.subtypeL =
      (ContinuousLinearEquiv.refl ℝ A : A →L[ℝ] A) := by
    ext1 x; exact hp' x
  rw [h3] at h2
  have h4 := h2.map_nhds_eq_of_equiv
  simp only [Submodule.coe_zero, h0, map_zero] at h4
  rw [← h4]
  have h6 : Subtype.val ⁻¹' W ∈ 𝓝 (0 : A) := continuous_subtype_val.continuousAt.preimage_mem_nhds hW
  refine mem_of_superset (image_mem_map h6) ?_
  rintro _ ⟨Y, hY, rfl⟩
  exact ⟨Y.1, Y.2, hY, (congrArg Subtype.val (hp' ⟨_, hA _ Y.2⟩)).symm⟩


open scoped Matrix.Norms.Frobenius in
theorem exists_log (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) {W : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hW : W ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ)) :
    ∀ᶠ a : A in 𝓝 0, ∃ Y ∈ A, Y ∈ W ∧ NormedSpace.exp Y - 1 = a.1 := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := Fin n) (R := ℝ) (α := ℂ)
  exact exists_preimage (M := Matrix (Fin n) (Fin n) ℂ) A (f := fun Y => NormedSpace.exp Y - 1)
    (HasStrictFDerivAt.sub_const (f := NormedSpace.exp) 1 CompactDualExists.exp_strict)
    (sub_eq_zero.2 (NormedSpace.exp_zero (𝔸 := Matrix (Fin n) (Fin n) ℂ)))
    (fun _ hX => exp_sub_one_mem A hA hX) hW

def expSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) (X : ↥(A ⊓ lieJ ε)) : algSub ε A hA :=
  ⟨expJ ε ⟨X.1, X.2.2⟩, exp_sub_one_mem A hA X.2.1⟩

theorem continuous_expSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : Continuous (expSub ε A hA) :=
  ((continuous_expJ ε).comp (continuous_subtype_val.subtype_mk _)).subtype_mk _

theorem expSub_image_mem_nhds (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) {U : Set ↥(A ⊓ lieJ ε)} (hU : U ∈ 𝓝 (0 : ↥(A ⊓ lieJ ε))) :
    expSub ε A hA '' U ∈ 𝓝 (1 : algSub ε A hA) := by
  obtain ⟨e, he, h0⟩ := UpqExpChart.exists_chart (n := Fin n)
  have hinj : Set.InjOn NormedSpace.exp e.source := he ▸ e.injOn
  have hs := e.open_source.mem_nhds h0
  obtain ⟨T, hT, hTU⟩ := (mem_nhds_subtype _ _ _).1 hU
  have h1 : expJ ε '' (Subtype.val ⁻¹' (T ∩ e.source)) ∈ 𝓝 (1 : UJ ε) :=
    expJ_image_mem_nhds ε (continuous_subtype_val.continuousAt.preimage_mem_nhds (inter_mem hT hs))
  have h2 : Subtype.val ⁻¹' (expJ ε '' (Subtype.val ⁻¹' (T ∩ e.source))) ∈ 𝓝 (1 : algSub ε A hA) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds h1
  have hc : Continuous fun g : algSub ε A hA => (⟨uMat g.1 - 1, g.2⟩ : A) :=
    (((continuous_uMat ε).comp continuous_subtype_val).sub continuous_const).subtype_mk _
  have h3 : Tendsto (fun g : algSub ε A hA => (⟨uMat g.1 - 1, g.2⟩ : A)) (𝓝 1) (𝓝 0) :=
    hc.tendsto' 1 0 (Subtype.ext (sub_self (1 : Matrix (Fin n) (Fin n) ℂ)))
  filter_upwards [h2, h3.eventually (exists_log A hA hs)] with g hg1 hg2
  obtain ⟨X, hX, hXg⟩ := hg1
  obtain ⟨Y, hYA, hY, hYg⟩ := hg2
  have h4 : NormedSpace.exp X.1 = uMat g.1 := congrArg uMat hXg
  have h5 : NormedSpace.exp Y = uMat g.1 := sub_left_injective hYg
  have h6 : X.1 = Y := hinj hX.2 hY (h4.trans h5.symm)
  exact ⟨⟨X.1, h6 ▸ hYA, X.2⟩, hTU hX.1, Subtype.ext hXg⟩

theorem finrank_eq (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) {d : ℕ}
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hs : ∀ X, (X ∈ A ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) :
    Module.finrank ℝ ↥(A ⊓ lieJ ε) = d := by
  have h1 : A ⊓ lieJ ε = Submodule.span ℝ (Set.range E) := Submodule.ext hs
  have h2 : LinearIndependent ℝ E := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h := congrArg (fun Z => ((Z * (E k)ᴴ).trace).re) hc
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum,
      Complex.smul_re, hE] at h
    simpa using h
  rw [h1, finrank_span_eq_card h2, Fintype.card_fin]


open scoped Matrix.Norms.Frobenius in
theorem exists_limit (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) (μ : Measure (algSub ε A hA)) [μ.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ Tendsto
      (fun r : ℝ => (μ {g | Real.sqrt (Formalism.REAL.hs (uMat g.1 - 1)) ≤ r}).toReal /
        r ^ Module.finrank ℝ ↥(A ⊓ lieJ ε)) (𝓝[>] 0) (𝓝 c) := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAddCommGroup
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAlgebra
  let L₀ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℝ _
  have hL₀ : Continuous L₀ := L₀.continuous_of_finiteDimensional
  have h := exists_limit_of_chart ↥(A ⊓ lieJ ε) (Matrix (Fin n) (Fin n) ℂ) (algSub ε A hA) μ
    (expSub ε A hA) (fun g => uMat g.1)
    (A ⊓ lieJ ε).subtypeₗᵢ (fun g => L₀ (uMat g.1)) (continuous_expSub ε A hA)
    (by
      apply Subtype.ext
      apply uMat_injective ε
      change NormedSpace.exp 0 = 1
      exact NormedSpace.exp_zero (𝔸 := Matrix (Fin n) (Fin n) ℂ))
    (by
      change HasStrictFDerivAt (fun x : ↥(A ⊓ lieJ ε) => NormedSpace.exp x.1)
        (A ⊓ lieJ ε).subtypeL 0
      exact CompactDualExists.exp_strict.comp
        (0 : ↥(A ⊓ lieJ ε)) (A ⊓ lieJ ε).subtypeL.hasStrictFDerivAt)
    (hL₀.comp ((continuous_uMat ε).comp continuous_subtype_val)).continuousAt
    (by
      change (L₀ 1) = ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℂ)
      ext X
      simp [L₀]) (fun g h => rfl)
    (fun r hr => expSub_image_mem_nhds ε A hA (ball_mem_nhds 0 hr))
    ((uJEmb n ε).1.isInducing.comp IsInducing.subtypeVal)
  simp only [sqrt_hs]
  exact h

theorem exists_isGaugeSub : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∃ μ : Measure (Formalism.REAL.UJ ε), SigmaFinite μ ∧ IsGaugeSub {g | uMat g - 1 ∈ A} d μ := by
  intro n ε A d E hA hE hs
  have hcl := isClosed_algSub ε A hA
  haveI : LocallyCompactSpace (algSub ε A hA) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hemb : MeasurableEmbedding (Subtype.val : algSub ε A hA → UJ ε) :=
    MeasurableEmbedding.subtype_coe hcl.measurableSet
  obtain ⟨c, hc, h⟩ := exists_limit ε A hA Measure.haar
  rw [finrank_eq ε A E hE hs] at h
  set B := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hBdef
  have hBt : B ≠ ⊤ := measure_ball_lt_top.ne
  have hB : 0 < B.toReal := ENNReal.toReal_pos (measure_ball_pos _ 0 one_pos).ne' hBt
  have hq : 0 < B.toReal / c := div_pos hB hc
  set ν : Measure (algSub ε A hA) := (B.toReal / c).toNNReal • Measure.haar with hν
  haveI : ν.IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul _ (Real.toNNReal_pos.2 hq).ne'
  haveI : SecondCountableTopology (algSub ε A hA) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  refine ⟨ν.map Subtype.val, hemb.sigmaFinite_map, ?_, fun s hs => ?_, ?_⟩
  · rw [hemb.map_apply]
    convert measure_empty (μ := ν)
    ext g
    exact ⟨fun hg => hg g.2, False.elim⟩
  · rw [Measure.map_map (measurable_const_mul s) hemb.measurable]
    conv_rhs => rw [← map_mul_left_eq_self ν (⟨s, hs⟩ : algSub ε A hA)]
    rw [Measure.map_map hemb.measurable (measurable_const_mul _)]
    rfl
  · have h1 := ENNReal.tendsto_ofReal (h.const_mul (B.toReal / c))
    rw [div_mul_cancel₀ _ hc.ne', ENNReal.ofReal_toReal hBt] at h1
    refine h1.congr' ?_
    filter_upwards [h.eventually (lt_mem_nhds hc), self_mem_nhdsWithin] with r h2 hr
    have hr' : (0 : ℝ) < r := hr
    have h3 := (ENNReal.toReal_pos_iff.1 ((div_pos_iff_of_pos_right (pow_pos hr' d)).1 h2)).2.ne
    rw [hemb.map_apply, hν, Measure.coe_nnreal_smul_apply, ENNReal.ofReal_mul hq.le,
      ENNReal.ofReal_div_of_pos (pow_pos hr' d), ENNReal.ofReal_toReal h3, mul_div_assoc]
    rfl

end GlobalTheory.GaugeSubExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvSubOneMem
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.GaugeSubLoc

variable {n : ℕ} {ε : Fin n → Bool}

theorem uMat_mul (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_one : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← uMat_mul, mul_inv_cancel, uMat_one]

theorem uMat_inv_mul (g : Formalism.REAL.UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  rw [← uMat_mul, inv_mul_cancel, uMat_one]

theorem inv_sub_one_mem (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A)
    (g : Formalism.REAL.UJ ε) (hg : uMat g - 1 ∈ A) : uMat g⁻¹ - 1 ∈ A := by

  have hmap : ∀ W : A, uMat g * (W : Matrix (Fin n) (Fin n) ℂ) ∈ A := by
    intro W
    have : uMat g * (W : Matrix (Fin n) (Fin n) ℂ) = (uMat g - 1) * W + W := by noncomm_ring
    rw [this]
    exact A.add_mem (hA _ hg _ W.2) W.2
  let T : A →ₗ[ℝ] A :=
    LinearMap.codRestrict A ((LinearMap.mulLeft ℝ (uMat g)).comp A.subtype) hmap
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro W hW
    have h0 : uMat g * (W : Matrix (Fin n) (Fin n) ℂ) = 0 := congrArg Subtype.val hW
    apply Subtype.ext
    calc (W : Matrix (Fin n) (Fin n) ℂ) = uMat g⁻¹ * (uMat g * W) := by
          rw [← Matrix.mul_assoc, uMat_inv_mul, Matrix.one_mul]
      _ = 0 := by rw [h0, Matrix.mul_zero]
  obtain ⟨W, hW⟩ := (LinearMap.injective_iff_surjective (f := T)).mp hinj ⟨-(uMat g - 1), A.neg_mem hg⟩
  have hW' : uMat g * (W : Matrix (Fin n) (Fin n) ℂ) = -(uMat g - 1) := congrArg Subtype.val hW
  have hinv : uMat g⁻¹ = 1 + (W : Matrix (Fin n) (Fin n) ℂ) := by
    calc uMat g⁻¹ = uMat g⁻¹ * (uMat g * (1 + (W : Matrix (Fin n) (Fin n) ℂ))) := by
          rw [Matrix.mul_add, Matrix.mul_one, hW', show uMat g + -(uMat g - 1) = 1 by abel,
            Matrix.mul_one]
      _ = 1 + (W : Matrix (Fin n) (Fin n) ℂ) := by
          rw [← Matrix.mul_assoc, uMat_inv_mul, Matrix.one_mul]
  rw [hinv, add_sub_cancel_left]
  exact W.2

def algSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : Subgroup (Formalism.REAL.UJ ε) where
  carrier := {g | uMat g - 1 ∈ A}
  one_mem' := by simp [uMat_one]
  mul_mem' := by
    intro g h hg hh
    have : uMat (g * h) - 1 = (uMat g - 1) * (uMat h - 1) + (uMat g - 1) + (uMat h - 1) := by
      rw [uMat_mul]; noncomm_ring
    change uMat (g * h) - 1 ∈ A
    rw [this]
    exact A.add_mem (A.add_mem (hA _ hg _ hh) hg) hh
  inv_mem' := fun {g} hg => inv_sub_one_mem A hA g hg

theorem isClosed_algSub (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : IsClosed (algSub ε A hA : Set (Formalism.REAL.UJ ε)) := by
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => uMat g - 1) :=
    (Units.continuous_val.comp continuous_subtype_val).sub continuous_const
  exact A.closed_of_finiteDimensional.preimage hc

end GlobalTheory.GaugeSubLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatExistsOfForms0
section
open Formalism.BasicNotions Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.St.Lat

theorem latExists_of_forms0 : ∀ D : D7, Formalism.L2.Forms.Forms0 D D.u₀ → LatExists D := by
  intro D hF
  refine GlobalTheory.St.Lat.latExists_of ?_ ?_ D ?_
  · exact _root_.GlobalTheory.HypPrimVec.exists_primitive_norm_neg
  · exact GlobalTheory.unramified_degree_one_of_ncard_placesOver
  · exact GlobalTheory.IsoOrthHyp.exists_isotropic_orth_hyp D hF

end GlobalTheory.St.Lat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MExistsHolds
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.St

theorem mExists_holds : ∀ D : D7, MExists D :=
  fun D => Formalism.L2.SG.Pf.mExists_of_cuts D weil_measure_compat infinite_measure_transfer

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUnique
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeConst

theorem gauge_exists_pos_unique :
    ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧ IsGauge ε c ∧ ∀ c', IsGauge ε c' → c' = c :=
  GlobalTheory.GaugeConst.exists_unique_isGauge

end GlobalTheory.GaugeConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeWholeGroup
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeWhole

private theorem pos_of_isGauge' {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) : 0 < c := by
  have h' : Filter.Tendsto
      (fun r : ℝ => c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal) := h
  have hpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  by_contra hc
  push_neg at hc
  have hle : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2) ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc ENNReal.toReal_nonneg)
      (pow_nonneg (le_of_lt hr) _)
  have := le_of_tendsto h' hle
  linarith

theorem isGaugeSub_univ {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) :
    0 < c ∧ IsGaugeSub (Set.univ : Set (Formalism.REAL.UJ ε)) (n ^ 2) (ENNReal.ofReal c • Formalism.REAL.muG ε) := by
  have hc := pos_of_isGauge' h
  have h' : Filter.Tendsto
      (fun r : ℝ => c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal) := h
  have hpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have hfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1) ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨hc, ?_⟩
  unfold IsGaugeSub
  refine ⟨by simp, fun s _ => ?_, ?_⟩
  · rw [Measure.map_smul, map_mul_left_eq_self]
    exact (measurable_const_smul s).aemeasurable
  · rw [← ENNReal.ofReal_toReal hfin]
    refine (ENNReal.tendsto_ofReal h').congr' ?_
    filter_upwards [h'.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    have hμ : Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
      intro htop
      rw [htop] at hr
      simp at hr
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_div_of_pos (pow_pos hr0' _),
      ENNReal.ofReal_mul hc.le, ENNReal.ofReal_toReal hμ]

theorem gauge_whole : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ c : ℝ, IsGauge ε c → 0 < c ∧ IsGaugeSub (Set.univ : Set (Formalism.REAL.UJ ε)) (n ^ 2) (ENNReal.ofReal c • Formalism.REAL.muG ε)) ∧ ∃ (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧ (Set.univ : Set (Formalism.REAL.UJ ε)) = {g | uMat g - 1 ∈ A} := by
  intro n ε
  refine ⟨fun c hc => isGaugeSub_univ hc, ?_⟩
  obtain ⟨E, hE, horth, hexp⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  refine ⟨⊤, E, fun _ _ _ _ => Submodule.mem_top, horth, fun X => ?_, ?_⟩
  · constructor
    · rintro ⟨-, hX⟩
      rw [hexp X hX]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hs : ((((X * (E i)ᴴ).trace).re : ℝ) : ℂ) • E i = (((X * (E i)ᴴ).trace).re : ℝ) • E i := by
        ext a b
        simp [Complex.real_smul]
      rw [hs]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro hX
      refine ⟨Submodule.mem_top, ?_⟩
      have hle : Submodule.span ℝ (Set.range E) ≤ GlobalTheory.GaugeConst.lieJ ε := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact GlobalTheory.GaugeConst.mem_lieJ.mpr (hE i).1
      exact GlobalTheory.GaugeConst.mem_lieJ.mp (hle hX)
  · ext g
    simp

end GlobalTheory.GaugeWhole
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoLeRootDiscriminantAndSplitArithmeticCondition
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem two_le_rdE_and_arithmeticConditionsS0 : ∀ D : D7, 2 ≤ D.host.rdE ∧ ArithmeticConditionsOfDatum D := fun D =>
  ⟨S.root_discriminant_ge_two _ (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _),
    fun u => S.splitsCompl_of_ncard _ _ (D.mem u).A.T_prime
      (Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion.split_clause _ Formalism.L2.SG.ResidEvFree.cycSplit_holds _ (D.mem u).A.T_prime (S.level_norm_one_mod_conductor _ u)).2,
    Formalism.L2.SG.ResidEvFree.splitsE_g _ 0, Formalism.L2.SG.ResidEvFree.splitsE_g _ 1, S.discriminant_eq_base_sq _ (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _)⟩

end GlobalTheory
end

