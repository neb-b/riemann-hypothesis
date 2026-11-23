module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Imports
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.level :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), Level W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ Φ hΦ
  obtain ⟨κ, hκc, hκ⟩ := finTr F E D
  have hfo : IsOpen {k | TR.finRep F 2 k f = f} := (π.cusp f hf).1.level
  have h1 : ∀ᶠ k in 𝓝 (1 : GL (Fin 2) (Af E)), TR.finRep F 2 (κ k) f = f := by
    have hm : {k | TR.finRep F 2 k f = f} ∈ 𝓝 (κ 1) := hfo.mem_nhds (by simp)
    exact hκc.continuousAt.eventually hm
  let S : Subgroup (GL (Fin 2) (Af E)) :=
    { carrier := {k | GlobalTheory.CuspRep.finRep E 2 k Φ = Φ}
      one_mem' := by simp
      mul_mem' := fun {k l} hk hl => by
        change GlobalTheory.CuspRep.finRep E 2 (k * l) Φ = Φ
        rw [map_mul, Module.End.mul_apply, hl, hk]
      inv_mem' := fun {k} hk => by
        change GlobalTheory.CuspRep.finRep E 2 k⁻¹ Φ = Φ
        conv_lhs => rw [← show GlobalTheory.CuspRep.finRep E 2 k Φ = Φ from hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl }
  refine Subgroup.isOpen_of_mem_nhds (H := S) (g := 1) ?_
  filter_upwards [lLevel F E D W φ, h1] with k hL hk
  refine Subtype.ext (funext fun g => ?_)
  change Φ.1 (g * finGL E 2 k) = Φ.1 g
  rw [hΦ, transl F E D W M, hL, hκ k]
  exact congrFun (congrArg (fun u => lift W M u φ) (congrArg Subtype.val hk)) g
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.IntegrableMulChar
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem der_nU {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D) {Ψ Ψ' : ℝ → S4 F}
    (h : Der Ψ Ψ') (b : A F) :
    Der (fun s => W.Om (nU b) (Ψ s)) (fun s => W.Om (nU b) (Ψ' s)) := by
  intro t v
  simp only [W.Om_n]
  exact (h t v).const_mul _

private theorem integrable_mul_char {F : Type} [Field F] [NumberField F] (φ : S4 F)
    {c : V4 F → ℂ} (hc : Continuous c) (hn : ∀ y, ‖c y‖ = 1) :
    Integrable (fun y => φ.1 y * c y) (adeleMeasurePi F) := by
  obtain ⟨N, hN⟩ := wtInt F
  obtain ⟨hφ, K, hK, hB⟩ := wtBound F φ
  obtain ⟨B, hB⟩ := hB N
  refine Integrable.mono' ((hN K hK).const_mul B) (hφ.mul hc).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [norm_mul, hn, mul_one]
  exact hB () (Set.mem_univ _) y

private theorem der_wW {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D) {Ψ Ψ' : ℝ → S4 F}
    (h : Der Ψ Ψ') (hd : ∀ t, Dom (Metric.ball t 1) fun s => (Ψ' s).1) :
    Der (fun s => W.Om (wW F) (Ψ s)) (fun s => W.Om (wW F) (Ψ' s)) := by
  intro t v
  simp only [W.Om_w, ft4]
  obtain ⟨N, hN⟩ := wtInt F
  obtain ⟨K, hK, hB⟩ := hd t
  obtain ⟨B, hB⟩ := hB N
  have e : ∀ i, Continuous fun y : V4 F => y i := fun i => continuous_apply i
  have cB : Continuous fun y : V4 F => B4 D.δ y v :=
    ((continuous_const.mul (((e 2).mul continuous_const).sub
      (continuous_const.mul ((e 3).mul continuous_const)))).sub
      ((e 1).mul continuous_const)).sub ((e 0).mul continuous_const)
  have cψ : Continuous fun y : V4 F => ψ (B4 D.δ y v) := continuous_ψ.comp cB
  have cont : ∀ φ : S4 F, Continuous fun y => φ.1 y * ψ (B4 D.δ y v) :=
    fun φ => (wtBound F φ).1.mul cψ
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s y => (Ψ s).1 y * ψ (B4 D.δ y v)) (F' := fun s y => (Ψ' s).1 y * ψ (B4 D.δ y v))
    (bound := fun y => B * wt K N y) (μ := adeleMeasurePi F)
    (Metric.ball_mem_nhds t one_pos)
    (Eventually.of_forall fun s => (cont (Ψ s)).aestronglyMeasurable)
    (integrable_mul_char (Ψ t) cψ fun y => norm_ψ _)
    (cont (Ψ' t)).aestronglyMeasurable
    (Eventually.of_forall fun y s hs => by
      rw [norm_mul, norm_ψ, mul_one]
      exact hB s hs y)
    ((hN K hK).const_mul B)
    (Eventually.of_forall fun y s _ => (h s y).mul_const _)).2

theorem UpperTheory.ConvolutionTheory.R2.Ff.omDer :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), OmDer W := by
  intro F E _ _ _ _ _ _ _ D W Ψ Ψ' h hd g
  have hg : g ∈ Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) := by
    rw [(gen F).1]
    trivial
  have wstep : ∀ y, Der (fun s => W.Om y (Ψ s)) (fun s => W.Om y (Ψ' s)) →
      Der (fun s => W.Om (wW F * y) (Ψ s)) (fun s => W.Om (wW F * y) (Ψ' s)) := by
    intro y hy
    simp only [map_mul, Module.End.mul_apply]
    exact der_wW W hy (hd y)
  induction hg using Subgroup.closure_induction_left with
  | one => simpa using h
  | mul_left x hx y _ ih =>
    rcases hx with ⟨b, rfl⟩ | hx
    · simp only [map_mul, Module.End.mul_apply]
      exact der_nU W ih b
    · rw [Set.mem_singleton_iff.1 hx]
      exact wstep y ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with ⟨b, rfl⟩ | hx
    · rw [← nU_neg]
      simp only [map_mul, Module.End.mul_apply]
      exact der_nU W ih (-b)
    · rw [Set.mem_singleton_iff.1 hx, wW_inv, ← wW_mul_wW, mul_assoc, mul_assoc]
      exact wstep _ (wstep _ (wstep y ih))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Iwa
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.iwa :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Iwa F := by
  intro F _ _ _
  obtain ⟨hK, hKc⟩ := M.kkCpt F
  obtain ⟨hB, e, he⟩ := M.borHomeo F
  refine ⟨hKc, fun C hC => ?_⟩
  have hemb : IsClosedEmbedding (Subtype.val : M.Bor F → G1 F) := hB.isClosedEmbedding_subtypeVal
  have hS : IsCompact ((fun p : G1 F × G1 F => p.1 * p.2) '' (C ×ˢ KK F)) :=
    (hC.prod hKc).image continuous_mul
  refine ⟨Prod.fst '' (e.symm '' ((Subtype.val : M.Bor F → G1 F) ⁻¹'
    ((fun p : G1 F × G1 F => p.1 * p.2) '' (C ×ˢ KK F)))),
    ((hemb.isCompact_preimage hS).image e.symm.continuous).image continuous_fst, fun g hg => ?_⟩
  obtain ⟨b, a, k, hk, rfl⟩ := M.iwa F g
  refine ⟨b, a, ?_, k, hk, rfl⟩
  refine ⟨(a, b), ⟨e (a, b), ?_, e.symm_apply_apply _⟩, rfl⟩
  change ((e (a, b) : M.Bor F) : G1 F) ∈ (fun p : G1 F × G1 F => p.1 * p.2) '' (C ×ˢ KK F)
  rw [he]
  refine ⟨(nU b * mD a * k, k⁻¹), ⟨hg, ?_⟩, by simp⟩
  change k⁻¹ ∈ KK F
  rw [hK] at hk ⊢
  exact (M.Ks F).inv_mem hk
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.SmCrit
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical ContDiff

namespace UpperTheory.ConvolutionTheory.R2.Ff

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

private noncomputable def invL (x : Lie E 2) : Lie E 2 := toL ((Matrix.of x)⁻¹)

private theorem invL_val (u : GL (Fin 2) (Cinf E)) : invL (toL u.val) = toL (u⁻¹).val := by
  simp [invL, Matrix.coe_units_inv]

private theorem contDiffOn_invL : ContDiffOn ℝ ∞ (invL (E := E)) (invSet E 2) := by
  have hdet : ContDiffOn ℝ ∞ (fun x : Lie E 2 => Ring.inverse (Matrix.of x).det) (invSet E 2) := by
    intro x hx
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hx
    have h1 : ContDiffAt ℝ ∞ (Ring.inverse : Cinf E → Cinf E) (Matrix.of x).det :=
      hu ▸ contDiffAt_ringInverse ℝ u
    exact (h1.comp x contDiff_det.contDiffAt).contDiffWithinAt
  have hent : ∀ i j, ContDiff ℝ ∞ fun x : Lie E 2 => x i j := fun i j =>
    (contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ i)
  have hadj : ∀ i j, ContDiff ℝ ∞ fun x : Lie E 2 => (Matrix.adjugate (Matrix.of x)) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two]
    · exact hent 1 1
    · exact (hent 0 1).neg
    · exact (hent 1 0).neg
    · exact hent 0 0
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  refine (hdet.mul (hadj i j).contDiffOn).congr fun x _ => ?_
  simp [invL, Matrix.inv_def]

private theorem chart_eq (Φ : GL (Fin 2) (A E) → ℂ) (g : GL (Fin 2) (A E)) (u : GL (Fin 2) (Cinf E)) :
    chart Φ g = chart Φ (g * infGL E 2 u) ∘ lmul (toL (u⁻¹).val) := by
  rw [← chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

private theorem fd {Φ : GL (Fin 2) (A E) → ℂ} {T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ)}
    (h : ∀ g, DifferentiableAt ℝ (chart Φ g) (oneL E 2) ∧ ∀ X, fderiv ℝ (chart Φ g) (oneL E 2) X = T X g)
    (g : GL (Fin 2) (A E)) (u : GL (Fin 2) (Cinf E)) :
    DifferentiableAt ℝ (chart Φ g) (toL u.val) ∧
      ∀ Z, fderiv ℝ (chart Φ g) (toL u.val) Z = T (lmul (toL (u⁻¹).val) Z) (g * infGL E 2 u) := by
  have e1 : lmul (toL (u⁻¹).val) (toL u.val) = oneL E 2 := u.inv_mul
  have hd : DifferentiableAt ℝ (chart Φ (g * infGL E 2 u)) (lmul (toL (u⁻¹).val) (toL u.val)) := by
    rw [e1]; exact (h _).1
  have hc := hd.comp (toL u.val) (lmul (toL (u⁻¹).val)).differentiableAt
  rw [← chart_eq] at hc
  refine ⟨hc, fun Z => ?_⟩
  rw [chart_eq Φ g u, fderiv_comp _ hd (lmul (toL (u⁻¹).val)).differentiableAt, e1,
    ContinuousLinearMap.fderiv]
  exact (h _).2 _

private theorem diffOn {Φ : GL (Fin 2) (A E) → ℂ} {T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ)}
    (h : ∀ g, DifferentiableAt ℝ (chart Φ g) (oneL E 2) ∧ ∀ X, fderiv ℝ (chart Φ g) (oneL E 2) X = T X g)
    (g : GL (Fin 2) (A E)) : DifferentiableOn ℝ (chart Φ g) (invSet E 2) := by
  intro x hx
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  exact (fd h g u).1.differentiableWithinAt

private theorem T_apply (T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ)) (b : Module.Basis (Fin (Module.finrank ℝ (Lie E 2))) ℝ (Lie E 2))
    (Y : Lie E 2) (h : GL (Fin 2) (A E)) : T Y h = ∑ j, (b.repr Y j) • T (b j) h := by
  conv_lhs => rw [← b.sum_repr Y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply]

private theorem smN (S : Submodule ℂ (GL (Fin 2) (A E) → ℂ))
    (hS : ∀ Φ ∈ S, ∃ T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ), (∀ X, T X ∈ S) ∧
      ∀ g, DifferentiableAt ℝ (chart Φ g) (oneL E 2) ∧ ∀ X, fderiv ℝ (chart Φ g) (oneL E 2) X = T X g)
    (n : ℕ) : ∀ Φ ∈ S, ∀ g, ContDiffOn ℝ n (chart Φ g) (invSet E 2) := by
  induction n with
  | zero =>
    intro Φ hΦ g
    obtain ⟨T, -, h⟩ := hS Φ hΦ
    rw [Nat.cast_zero]
    exact contDiffOn_zero.2 (diffOn h g).continuousOn
  | succ n ih =>
    intro Φ hΦ g
    obtain ⟨T, hT, h⟩ := hS Φ hΦ
    rw [Nat.cast_add, Nat.cast_one]
    refine (contDiffOn_succ_iff_fderiv_of_isOpen isOpen_invSet).2 ⟨diffOn h g, by simp, ?_⟩
    refine contDiffOn_clm_apply.2 fun Z => ?_
    let b := Module.finBasis ℝ (Lie E 2)
    have hinv : ContDiffOn ℝ n (invL (E := E)) (invSet E 2) :=
      contDiffOn_invL.of_le (by exact_mod_cast le_top)
    have key : ContDiffOn ℝ n (fun x => ∑ j, (b.repr (rmul Z (invL x)) j) • chart (T (b j)) g x) (invSet E 2) :=
      ContDiffOn.sum fun j _ => ContDiffOn.smul
        ((LinearMap.toContinuousLinearMap (b.coord j)).contDiff.comp_contDiffOn
          ((rmul Z).contDiff.comp_contDiffOn hinv)) (ih _ (hT _) g)
    refine key.congr fun x hx => ?_
    obtain ⟨u, hu⟩ := id hx
    obtain rfl : x = toL u.val := hu.symm
    rw [(fd h g u).2 Z, T_apply T b, invL_val]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [chart_val]
    rfl

end UpperTheory.ConvolutionTheory.R2.Ff

theorem UpperTheory.ConvolutionTheory.R2.Ff.smCrit :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], SmCrit E := by
  intro E _ _ _ S hc hd Φ hΦ g
  refine contDiffOn_infty.2 fun n => smN S (fun Φ hΦ => ?_) n Φ hΦ g
  obtain ⟨T, hT, h⟩ := hd Φ hΦ
  exact ⟨T, hT, smFre E Φ T (fun X g => hc _ (hT X) g) h⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThMeas
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem measurable_tsum_complex {ι X : Type} [Countable ι] [MeasurableSpace X] (f : ι → X → ℂ)
    (hf : ∀ i, Measurable (f i)) : Measurable fun x => ∑' i, f i x := by
  have hS : MeasurableSet {x | Summable fun i => f i x} := by
    have hm : Measurable fun x => ∑' i, (‖f i x‖₊ : ENNReal) :=
      Measurable.tsum fun i => (hf i).nnnorm.coe_nnreal_ennreal
    have : {x | Summable fun i => f i x} = (fun x => ∑' i, (‖f i x‖₊ : ENNReal)) ⁻¹' Set.Iio ⊤ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio, lt_top_iff_ne_top]
      rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
      simp only [coe_nnnorm]
      exact summable_norm_iff.symm
    rw [this]
    exact hm measurableSet_Iio
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset ι))
    (f := fun s => Set.indicator {x | Summable fun i => f i x} fun x => ∑ i ∈ s, f i x)
    (fun s => (Finset.measurable_sum s fun i _ => hf i).indicator hS) ?_
  rw [tendsto_pi_nhds]
  intro x
  by_cases hx : Summable fun i => f i x
  · have h : Tendsto (fun s : Finset ι => ∑ i ∈ s, f i x) atTop (𝓝 (∑' i, f i x)) := by
      simpa [HasSum] using hx.hasSum
    simpa [Set.indicator, hx] using h
  · simp [Set.indicator, hx, tsum_eq_zero_of_not_summable hx, tendsto_const_nhds]

theorem UpperTheory.ConvolutionTheory.R2.Ff.thMeas :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ThMeas W := by
  intro F E _ _ _ _ _ _ _ D W φ
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hpt : ∀ v, Measurable fun g => (W.Om g φ).1 v := fun v =>
    ((W.cont φ).comp (continuous_id.prodMk continuous_const)).measurable
  have hψ : Continuous (ψ : A F → ℂ) := continuous_subtype_val.comp (continuous_adelicChar (K := F))
  have hhat : ∀ v, Measurable fun g => hat (W.Om g φ).1 v := by
    intro v
    have hc : Continuous fun p : G1 F × A F =>
        (W.Om p.1 φ).1 (Function.update v 1 p.2) * ψ (-(p.2 * v 1)) :=
      ((W.cont φ).comp (continuous_fst.prodMk (continuous_const.update 1 continuous_snd))).mul
        (hψ.comp (continuous_snd.mul continuous_const).neg)
    exact (hc.stronglyMeasurable.integral_prod_right' (ν := adeleMeasure F)).measurable
  refine ⟨?_, ?_, ?_, ?_, hhat⟩
  · exact measurable_tsum_complex _ fun ξ => hpt _
  · intro γ g
    simp only [map_mul, Module.End.mul_apply]
    exact W.th_Om γ _
  · intro r₀ r₁
    exact measurable_tsum_complex _ fun ξ => hhat _
  · intro γ g
    have h := (hatSt F E D W).row γ 0 (W.Om g φ)
    simp only [map_mul, Module.End.mul_apply]
    simpa using h
end

