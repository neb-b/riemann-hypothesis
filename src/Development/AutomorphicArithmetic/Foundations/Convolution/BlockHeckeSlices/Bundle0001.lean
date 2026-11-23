module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CapRDefs
section
noncomputable section

open MeasureTheory NumberField GlobalTheory.CuspRep
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

abbrev onQ (h : GA E r → ℂ) (y : RightCosetSpace (rationalGLOne (K := E) (n := r))) : ℂ := h ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r)

abbrev muQ (E : Type) [Field E] [NumberField E] (r : ℕ) : Measure (RightCosetSpace (rationalGLOne (K := E) (n := r))) :=
  quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r)

def pr (Φ f : GA E r → ℂ) : ℂ := ∫ y, onQ Φ y * starRingEnd ℂ (onQ f y) ∂muQ E r

def j0 (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r : ℕ) : Module.End ℂ (Sm E r) :=
  ((r * Module.finrank ℚ E : ℕ) : ℂ)⁻¹ • ∑ τ : E →+* ℂ, ∑ i : Fin r, Eop τ i i

end UpperTheory.ConvolutionTheory.BW
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatDatum
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx UpperTheory.ConvolutionTheory.C

namespace UpperTheory.ConvolutionTheory.BW

structure Rep {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (μ : Measure (normOneGL (K := E) (n := n)))
    (v : LL μ) (φ : Sm E n) : Prop where
  umg : Umg φ
  cen : ∀ t g, φ.1 (zt E n t * g) = φ.1 g
  ae : (v : RightCosetSpace (rationalGLOne (K := E) (n := n)) → ℂ) =ᵐ[quotientMeasure (rationalGLOne (K := E) (n := n)) μ]
    fun y => φ.1 ((Quotient.out y : normOneGL (K := E) (n := n)) : GA E n)

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def RepOps : Prop := ∀ (n : ℕ) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure], 0 < n → ∀ (v : LL μ) (φ : Sm E n), Rep μ v φ →
  (∀ ψ, Rep μ v ψ → φ = ψ) ∧ (∀ (v' : LL μ) ψ (c : ℂ), Rep μ v' ψ → Rep μ (c • v + v') (c • φ + ψ)) ∧
  (Cusp φ.1 → v ∈ cuspidalL2 μ) ∧
  ∀ (w : Pl E) (i : Fin n), (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), rw n w k φ = φ) → Rep μ (Tsph μ w i v) (hk n w (i + 1) φ)

def AmpRep : Prop := ∀ (n : ℕ) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (𝔞 : Amp μ), 0 < n →
  ∃ (ρ : Typ E n) (N : ℕ) (L : LL μ →ₗ[ℂ] Sm E n),
    (∀ v, Rep μ (𝔞.A v) (L v) ∧ Killed ρ.ρ (L v).1 ∧ Sph 𝔞.S (L v)) ∧
    (∀ u : UpperTheory.V.Cm.UC E n, ∃ B : ℝ, ∀ v g, ‖(UpperTheory.V.Cm.uC E n u (L v)).1 g‖ ≤ B * ‖v‖ * AutomorphicForm.height g ^ N) ∧
    ∀ x v, Rep μ (𝔞.Z x v) (zop (MvPolynomial.X x) (L v))

def DatDatum : Prop := ∀ (S : Set (Pl E)) (n : ℕ) (d : Dat S n), 2 ≤ d.len → ∃ b : Datum E n, (∃ Λ t, b.Pt S Λ t) ∧
  ∀ F : KF (Ix E n) (UpperTheory.ConvolutionTheory.Pl E × Fin n), (∀ x ∈ F.vars, x.1 ∉ S) → Kills S F b → d.Kills F

def BandRep : Prop := ∀ (n : ℕ) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (𝔞 : Amp μ) (η : ℝ), 0 < n → 0 < η →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ χ : ℝ → ℝ, Continuous χ → (∀ x ≤ η / 2, χ x = 0) → ∀ (u : LL μ) (φ : Sm E n),
    Rep μ (fcalc χ 𝔞.A u) φ → Band C φ

end UpperTheory.ConvolutionTheory.BW
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.IntegrableChart
section
noncomputable section

open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.ConstTermSmooth UpperTheory.V.Cm
open scoped ContDiff

namespace UpperTheory.ConvolutionTheory.BW.SliceClasses

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
  {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (p : Y → GA E a) (w : Y → ℂ)

def avg (F : GA E a → ℂ) (g : GA E a) : ℂ := ∫ y, F (p y * g) * w y ∂ν

structure Cls (Gd : Sm E a → Prop) : Prop where
  lie : ∀ F X, Gd F → Gd (lie E a X F)
  meas : ∀ F, Gd F → ∀ g, AEStronglyMeasurable (fun y => F.1 (p y * g) * w y) ν
  bdd : ∀ F, Gd F → ∀ K : Set (GA E a), IsCompact K → ∃ C : ℝ, ∀ y, ∀ g ∈ K, ‖F.1 (p y * g) * w y‖ ≤ C

variable {ν p w} {Gd : Sm E a → Prop} [IsFiniteMeasure ν]

theorem Cls.integrable (h : Cls ν p w Gd) {F : Sm E a} (hF : Gd F) (g : GA E a) :
    Integrable (fun y => F.1 (p y * g) * w y) ν := by
  obtain ⟨C, hC⟩ := h.bdd F hF {g} isCompact_singleton
  exact Integrable.of_bound (h.meas F hF g) C (.of_forall fun y => hC y g rfl)

private theorem chart_unit (F : GA E a → ℂ) (g g' : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart F (g' * g) x = F (g' * (g * infGL E a (IsUnit.unit (hx : IsUnit (Matrix.of x))))) := by
  rw [← mul_assoc]
  exact chart_val F _ (IsUnit.unit (hx : IsUnit (Matrix.of x)))

private theorem Cls.integrable_chart (h : Cls ν p w Gd) {F : Sm E a} (hF : Gd F) (g : GA E a) {x : Lie E a}
    (hx : x ∈ invSet E a) : Integrable (fun y => chart F.1 (p y * g) x * w y) ν := by
  simp only [chart_unit F.1 g _ hx]
  exact h.integrable hF _

private theorem Cls.bdd_chart (h : Cls ν p w Gd) {F : Sm E a} (hF : Gd F) (g : GA E a) {S : Set (Lie E a)}
    (hS : IsCompact S) (hSU : S ⊆ invSet E a) : ∃ C : ℝ, ∀ y, ∀ x ∈ S, ‖chart F.1 (p y * g) x * w y‖ ≤ C := by
  have hu : Continuous fun x : S => (IsUnit.unit (hSU x.2 : IsUnit (Matrix.of x.1)) : GL (Fin a) (Cinf E)) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have := contDiffOn_invM.continuousOn.comp_continuous (f := fun x : S => x.1) continuous_subtype_val fun x => hSU x.2
    refine Continuous.congr this fun p => ?_
    simp only [Matrix.coe_units_inv]
    rfl
  haveI : CompactSpace S := isCompact_iff_compactSpace.1 hS
  obtain ⟨C, hC⟩ := h.bdd F hF _ (isCompact_range ((continuous_const (y := g)).mul (continuous_infGL.comp hu)))
  refine ⟨C, fun y x hx => ?_⟩
  rw [chart_unit F.1 g _ (hSU hx)]
  exact hC y _ ⟨⟨x, hx⟩, rfl⟩

omit [IsFiniteMeasure ν] in
private theorem chart_avg (F : GA E a → ℂ) (g : GA E a) :
    chart (avg ν p w F) g = fun x => ∫ y, chart F (p y * g) x * w y ∂ν := by
  funext x
  by_cases h : IsUnit (Matrix.of x)
  · simp only [chart, avg, dif_pos h, mul_assoc]
  · simp only [chart, dif_neg h, zero_mul, integral_zero]

private theorem Cls.hasFDerivAt (h : Cls ν p w Gd) {F : Sm E a} (hF : Gd F) (g : GA E a) {x : Lie E a}
    (hx : x ∈ invSet E a) : HasFDerivAt (chart (avg ν p w F.1) g)
      (∑ i, chart (avg ν p w (GlobalTheory.CuspRep.lie E a (Module.finBasis ℝ (Lie E a) i) F).1) g x • coef i x) x := by
  obtain ⟨S, hSy, hSU, hS⟩ := local_compact_nhds (isOpen_invSet.mem_nhds hx)
  choose C hC using fun i => h.bdd_chart (h.lie F (Module.finBasis ℝ (Lie E a) i) hF) g hS hSU
  choose D hD using fun i => hS.exists_bound_of_continuousOn ((contDiffOn_coef (E := E) (a := a) i).continuousOn.mono hSU)
  have hi : ∀ i, Integrable (fun y => (chart (GlobalTheory.CuspRep.lie E a (Module.finBasis ℝ (Lie E a) i) F).1 (p y * g) x * w y) • coef i x) ν :=
    fun i => (h.integrable_chart (h.lie F _ hF) g hx).smul_const _
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := fun x y => chart F.1 (p y * g) x * w y)
    (F' := fun x y => ∑ i, (chart (GlobalTheory.CuspRep.lie E a (Module.finBasis ℝ (Lie E a) i) F).1 (p y * g) x * w y) • coef i x)
    (bound := fun _ => ∑ i, C i * D i) hSy
    (Filter.eventually_of_mem (isOpen_invSet.mem_nhds hx) fun z hz => (h.integrable_chart hF g hz).1)
    (h.integrable_chart hF g hx) (integrable_finsetSum _ fun i _ => hi i).1
    (.of_forall fun y z hz => (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by
      rw [norm_smul]
      exact mul_le_mul (hC i y z hz) (hD i z hz) (norm_nonneg _) ((norm_nonneg _).trans (hC i y z hz))))
    (integrable_const _) (.of_forall fun y z hz => by
      have h1 := (((contDiffAt_chart F.2 (p y * g) (hSU hz)).differentiableAt (by simp)).hasFDerivAt).mul_const (w y)
      rw [fderiv_chart F _ (hSU hz), Finset.smul_sum] at h1
      simp only [smul_smul, mul_comm (w y)] at h1
      exact h1)
  rw [integral_finsetSum _ fun i _ => hi i] at key
  simp only [integral_smul_const] at key
  simp only [chart_avg]
  exact key

theorem Cls.mem_Sm (h : Cls ν p w Gd) {F : Sm E a} (hF : Gd F) : avg ν p w F.1 ∈ Sm E a := by
  intro g
  have key : ∀ n : ℕ, ∀ F : Sm E a, Gd F → ContDiffOn ℝ n (chart (avg ν p w F.1) g) (invSet E a) := by
    intro n
    induction n with
    | zero =>
      intro F hF
      exact contDiffOn_zero.2 fun y hy => (h.hasFDerivAt hF g hy).continuousAt.continuousWithinAt
    | succ n ih =>
      intro F hF
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_invSet]
      refine ⟨fun y hy => (h.hasFDerivAt hF g hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      refine ContDiffOn.congr ?_ fun y hy => (h.hasFDerivAt hF g hy).fderiv
      exact ContDiffOn.sum fun i _ => (ih _ (h.lie _ _ hF)).smul ((contDiffOn_coef i).of_le (by exact_mod_cast le_top))
  exact contDiffOn_infty.2 fun n => key n F hF

theorem Cls.lieD_avg (h : Cls ν p w Gd) {F : Sm E a} (hF : Gd F) (X : Lie E a) (g : GA E a) :
    lieD X (avg ν p w F.1) g = avg ν p w (GlobalTheory.CuspRep.lie E a X F).1 g := by
  have h1 : oneL E a ∈ invSet E a := isUnit_one
  rw [lieD, (h.hasFDerivAt hF g h1).fderiv]
  simp only [chart_avg, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ← integral_mul_const]
  rw [← integral_finsetSum _ fun i _ => (h.integrable_chart (h.lie F _ hF) g h1).mul_const _]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [lie_apply, lieD]
  rw [fderiv_chart F _ h1]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

end UpperTheory.ConvolutionTheory.BW.SliceClasses
end
end

