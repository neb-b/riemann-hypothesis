module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsBasic
section
noncomputable section

open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

section HS

variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem hsA_smul (c : ℂ) (A : V' →L[ℂ] V) : hsA (c • A) = ‖c‖ ^ 2 * hsA A := by
  unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.smul_apply, norm_smul, mul_pow]

private theorem sum_norm_inner_stdBasis_sq_eq_norm_sq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (x : E) :
    ∑ i, ‖⟪stdOrthonormalBasis ℂ E i, x⟫_ℂ‖ ^ 2 = ‖x‖ ^ 2 := by
  exact (stdOrthonormalBasis ℂ E).sum_sq_norm_inner_right x

theorem hsA_eq_adjoint (A : V' →L[ℂ] V) :
    hsA A = ∑ i, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V i)‖ ^ 2 := by
  unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
  calc ∑ i, ‖A (stdOrthonormalBasis ℂ V' i)‖ ^ 2
      = ∑ i, ∑ j, ‖⟪stdOrthonormalBasis ℂ V j, A (stdOrthonormalBasis ℂ V' i)⟫_ℂ‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sum_norm_inner_stdBasis_sq_eq_norm_sq]
    _ = ∑ j, ∑ i, ‖⟪stdOrthonormalBasis ℂ V' i,
          (ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V j)⟫_ℂ‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
    _ = ∑ j, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V j)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sum_norm_inner_stdBasis_sq_eq_norm_sq]

private theorem norm_sq_apply_of_inner_preserving {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E →L[ℂ] E) (hU : ∀ a b, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ) (v : E) : ‖U v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h := hU v v
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

theorem hsA_conj (U : V →L[ℂ] V) (U' : V' →L[ℂ] V') (hU : ∀ a b, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hU' : ∀ a b, ⟪U' a, U' b⟫_ℂ = ⟪a, b⟫_ℂ) (A : V' →L[ℂ] V) :
    hsA (U.comp (A.comp (ContinuousLinearMap.adjoint U'))) = hsA A := by
  have h1 : Formalism.L2.SG.Pf.EnergyAbs.hsA (U.comp (A.comp (ContinuousLinearMap.adjoint U'))) =
      Formalism.L2.SG.Pf.EnergyAbs.hsA (A.comp (ContinuousLinearMap.adjoint U')) := by
    unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.comp_apply]
    exact norm_sq_apply_of_inner_preserving U hU _
  rw [h1, hsA_eq_adjoint, hsA_eq_adjoint A]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply]
  exact norm_sq_apply_of_inner_preserving U' hU' _

def hsL : (V' →L[ℂ] V) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ V') => V) where
  toFun A := WithLp.toLp 2 (fun j => A (stdOrthonormalBasis ℂ V' j))
  map_add' A B := by
    ext j
    simp
  map_smul' c A := by
    ext j
    simp

def hsC : (V' →L[ℂ] V) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ V') => V) :=
  LinearMap.toContinuousLinearMap hsL

theorem norm_hsC (A : V' →L[ℂ] V) : ‖hsC A‖ = Real.sqrt (hsA A) := by
  rw [PiLp.norm_eq_of_L2]
  rfl

theorem sqrt_hsA_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → (V' →L[ℂ] V))
    (hf : Integrable f μ) :
    Real.sqrt (hsA (∫ x, f x ∂μ)) ≤ ∫ x, Real.sqrt (hsA (f x)) ∂μ := by
  simp_rw [← norm_hsC]
  rw [← ContinuousLinearMap.integral_comp_comm _ hf]
  exact norm_integral_le_integral_norm _

theorem sqrt_hsA_le_add_sub (A B : V' →L[ℂ] V) :
    Real.sqrt (hsA A) ≤ Real.sqrt (hsA B) + Real.sqrt (hsA (A - B)) := by
  simp_rw [← norm_hsC]
  have h : hsC A = hsC B + hsC (A - B) := by
    simp [map_sub]
  rw [h]
  exact norm_add_le _ _

end HS

section Rep

variable {G : Type} [Group G] [TopologicalSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH]

theorem rep_mul_apply {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (x y : G) (a : HH) :
    σ x (σ y a) = σ (x * y) a := by
  obtain ⟨-, hmul, -, -⟩ := hσ
  rw [hmul, ContinuousLinearMap.mul_apply]

end Rep

section Kernel

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

end Kernel

section Quot

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

theorem quot_map_inv {μ μS ν : Measure G} [SFinite ν] [SFinite μS] (hq : IsQuot μ μS ν)
    (hinv : μS.map (fun x => x⁻¹) = μS) :
    μ = (ν.prod μS).map (fun p => p.2⁻¹ * p.1) := by
  have hm : Measurable (fun p : G × G => p.2⁻¹ * p.1) := measurable_snd.inv.mul measurable_fst
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs)]
  have h := hq (s.indicator 1) (measurable_one.indicator hs)
  rw [lintegral_indicator_one hs] at h
  rw [h]
  refine lintegral_congr fun x => ?_
  have hx : MeasurableSet ((fun t : G => t * x) ⁻¹' s) := measurable_mul_const x hs
  have hx' : MeasurableSet ((fun t : G => t⁻¹ * x) ⁻¹' s) := (measurable_inv.mul_const x) hs
  calc ∫⁻ t, s.indicator (1 : G → ℝ≥0∞) (t * x) ∂μS
      = ∫⁻ t, ((fun t : G => t * x) ⁻¹' s).indicator (1 : G → ℝ≥0∞) t ∂μS := rfl
    _ = μS ((fun t : G => t * x) ⁻¹' s) := lintegral_indicator_one hx
    _ = (μS.map (fun t => t⁻¹)) ((fun t : G => t⁻¹ * x) ⁻¹' s) := by
        rw [Measure.map_apply measurable_inv hx']
        congr 1
        ext t
        simp
    _ = μS ((fun t : G => t⁻¹ * x) ⁻¹' s) := by rw [hinv]
    _ = _ := rfl

end Quot

end Formalism.L2.S.Pv.EnergyAbs
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsDefs
section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Formalism.L2.S.Pv.EnergyAbs

variable {G : Type} [Group G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def yv (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G) (e : V) : HH :=
  ∫ z, ∫ s in Ω, ⟪W (s⁻¹ * z), e⟫_ℂ • σ (s⁻¹ * z) w ∂μS ∂ν

def Yop (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G) : V →L[ℂ] HH :=
  ∑ i, (innerSL ℂ (stdOrthonormalBasis ℂ V i)).smulRight (yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i))

theorem Yop_apply (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G) (e : V) :
    Yop μS ν σ w W Ω e =
      ∑ i, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i) := by
  simp only [Yop, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

theorem Yop_apply_basis (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G)
    (j : Fin (Module.finrank ℂ V)) :
    Yop μS ν σ w W Ω (stdOrthonormalBasis ℂ V j) = yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V j) := by
  rw [Yop_apply, Finset.sum_eq_single j]
  · rw [orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ V).orthonormal]; simp
  · intro i _ hij
    rw [orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ V).orthonormal, if_neg hij, zero_smul]
  · intro h; exact absurd (Finset.mem_univ j) h

end Formalism.L2.S.Pv.EnergyAbs
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsFolnerConv
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

def cnt (μS : Measure G) (Ω : Set G) (q : G) : ℝ≥0∞ := μS {t | t ∈ Ω ∧ q * t ∈ Ω}

theorem cnt_measurable {μS : Measure G} [SFinite μS] {Ω : Set G} (hΩ : MeasurableSet Ω) :
    Measurable (cnt μS Ω) := by
  have hT : MeasurableSet {p : G × G | p.2 ∈ Ω ∧ p.1 * p.2 ∈ Ω} :=
    (measurable_snd hΩ).inter ((measurable_fst.mul measurable_snd) hΩ)
  exact measurable_measure_prodMk_left hT

theorem cnt_le (μS : Measure G) (Ω : Set G) (q : G) : cnt μS Ω q ≤ μS Ω := measure_mono fun t ht => ht.1

theorem conv_map {S : Set G} {μS : Measure G} [SFinite μS] (hS : IsHaarSub S μS) {Ω : Set G}
    (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) :
    ((μS.restrict Ω).prod (μS.restrict Ω)).map (fun p : G × G => p.1 * p.2⁻¹) = μS.withDensity (cnt μS Ω) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, hright, -⟩ := hS
  have hg : Measurable (fun p : G × G => p.1 * p.2⁻¹) := measurable_fst.mul measurable_snd.inv
  ext A hA
  rw [Measure.map_apply hg hA, withDensity_apply _ hA]
  set P : Set (G × G) := {p | p.1 ∈ A ∧ p.2 ∈ Ω ∧ p.1 * p.2 ∈ Ω} with hPdef
  have hP : MeasurableSet P :=
    (measurable_fst hA).inter ((measurable_snd hΩm).inter ((measurable_fst.mul measurable_snd) hΩm))
  have h1 : (μS.prod μS) P = ∫⁻ q in A, cnt μS Ω q ∂μS := by
    rw [Measure.prod_apply hP, ← lintegral_indicator hA]
    refine lintegral_congr fun q => ?_
    rw [Set.indicator_apply]
    by_cases hq : q ∈ A
    · rw [if_pos hq]
      unfold cnt
      congr 1
      ext t
      simp [hPdef, hq]
    · rw [if_neg hq]
      have hempty : Prod.mk q ⁻¹' P = ∅ := by
        ext t
        simp [hPdef, hq]
      rw [hempty, measure_empty]
  have h2 : (μS.prod μS) P =
      ((μS.restrict Ω).prod (μS.restrict Ω)) ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) := by
    rw [Measure.prod_apply_symm hP, Measure.prod_apply_symm (hg hA), ← lintegral_indicator hΩm]
    refine lintegral_congr fun t => ?_
    rw [Set.indicator_apply]
    by_cases ht : t ∈ Ω
    · rw [if_pos ht]
      have hBt : MeasurableSet
          ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A)) :=
        (measurable_mul_const t⁻¹) hA
      rw [Measure.restrict_apply hBt]
      have hmt := hright t (hΩS ht)
      calc μS ((fun x => (x, t)) ⁻¹' P)
          = μS ((fun x => x * t) ⁻¹'
              ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) ∩ Ω)) := by
            congr 1
            ext q
            simp [hPdef, ht]
        _ = (μS.map (fun x => x * t))
              ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) ∩ Ω) :=
            (Measure.map_apply (measurable_mul_const t) (hBt.inter hΩm)).symm
        _ = μS ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) ∩ Ω) := by
            rw [hmt]
    · rw [if_neg ht]
      have hempty : (fun x => (x, t)) ⁻¹' P = ∅ := by
        ext q
        simp [hPdef, ht]
      rw [hempty, measure_empty]
  exact h2.symm.trans h1

theorem conv_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set G} {μS : Measure G} [SFinite μS]
    (hS : IsHaarSub S μS) {Ω : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) (hfin : μS Ω < ⊤) (f : G → E)
    (hf : StronglyMeasurable f)
    (hint : Integrable (fun p : G × G => f (p.1 * p.2⁻¹)) ((μS.restrict Ω).prod (μS.restrict Ω))) :
    ∫ s in Ω, ∫ t in Ω, f (s * t⁻¹) ∂μS ∂μS = ∫ q, (cnt μS Ω q).toReal • f q ∂μS := by
  have hg : Measurable (fun p : G × G => p.1 * p.2⁻¹) := measurable_fst.mul measurable_snd.inv
  have hI : Integrable (fun p : G × G => f (p.1 * p.2⁻¹)) ((μS.restrict Ω).prod (μS.restrict Ω)) := by
    assumption
  have h1 : ∫ s in Ω, ∫ t in Ω, f (s * t⁻¹) ∂μS ∂μS
      = ∫ p, f (p.1 * p.2⁻¹) ∂((μS.restrict Ω).prod (μS.restrict Ω)) :=
    (integral_prod (fun p : G × G => f (p.1 * p.2⁻¹)) hI).symm
  have h2 : ∫ p, f (p.1 * p.2⁻¹) ∂((μS.restrict Ω).prod (μS.restrict Ω))
      = ∫ q, f q ∂(((μS.restrict Ω).prod (μS.restrict Ω)).map (fun p : G × G => p.1 * p.2⁻¹)) :=
    (integral_map_of_stronglyMeasurable hg hf).symm
  rw [h1, h2, conv_map hS hΩm hΩS]
  exact integral_withDensity_eq_integral_toReal_smul (cnt_measurable hΩm)
    (ae_of_all _ fun q => (cnt_le μS Ω q).trans_lt hfin) f

end Formalism.L2.S.Pv.EnergyAbs
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsSchur
section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def sand (σ : G → (HH →L[ℂ] HH)) (Y : V →L[ℂ] HH) (Y' : V' →L[ℂ] HH) (γ : G) : V' →L[ℂ] V :=
  (ContinuousLinearMap.adjoint Y).comp ((σ γ).comp Y')

theorem inner_sand (σ : G → (HH →L[ℂ] HH)) (Y : V →L[ℂ] HH) (Y' : V' →L[ℂ] HH) (γ : G) (a : V) (b : V') :
    ⟪a, sand σ Y Y' γ b⟫_ℂ = ⟪Y a, σ γ (Y' b)⟫_ℂ := by
  exact ContinuousLinearMap.adjoint_inner_right Y a (σ γ (Y' b))

private theorem norm_sq_eq_sum_norm_inner_stdBasis_sq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (v : E) :
    ‖v‖ ^ 2 = ∑ i, ‖⟪stdOrthonormalBasis ℂ E i, v⟫_ℂ‖ ^ 2 := by
  exact ((stdOrthonormalBasis ℂ E).sum_sq_norm_inner_right v).symm

theorem hsA_eq (A : V' →L[ℂ] V) :
    hsA A = ∑ j, ∑ i, ‖⟪stdOrthonormalBasis ℂ V i, A (stdOrthonormalBasis ℂ V' j)⟫_ℂ‖ ^ 2 := by
  show ∑ j, ‖A (stdOrthonormalBasis ℂ V' j)‖ ^ 2 = _
  exact Finset.sum_congr rfl fun j _ => norm_sq_eq_sum_norm_inner_stdBasis_sq _

theorem hsA_sand (σ : G → (HH →L[ℂ] HH)) (Y : V →L[ℂ] HH) (Y' : V' →L[ℂ] HH) (γ : G) :
    hsA (sand σ Y Y' γ) = ∑ j, ∑ i,
      ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2 := by
  rw [hsA_eq]
  simp only [inner_sand]

theorem norm_sq_eq_re_mul_conj (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

theorem schur_sq {μ : Measure G} {σ : G → (HH →L[ℂ] HH)} {d : ℝ} (hS : IsSchur μ σ d) (a b : HH) :
    Integrable (fun γ => ‖⟪a, σ γ b⟫_ℂ‖ ^ 2) μ ∧
      ∫ γ, ‖⟪a, σ γ b⟫_ℂ‖ ^ 2 ∂μ = ‖a‖ ^ 2 * ‖b‖ ^ 2 / d := by
  obtain ⟨hI, hE⟩ := hS.2 b a b a
  have hfun : (fun γ => ‖⟪a, σ γ b⟫_ℂ‖ ^ 2) =
      fun γ => RCLike.re (⟪a, σ γ b⟫_ℂ * conj ⟪a, σ γ b⟫_ℂ) := by
    funext γ
    exact norm_sq_eq_re_mul_conj _
  have h2 : ∫ γ, RCLike.re (⟪a, σ γ b⟫_ℂ * conj ⟪a, σ γ b⟫_ℂ) ∂μ =
      RCLike.re (⟪b, b⟫_ℂ * ⟪a, a⟫_ℂ / (d : ℂ)) := by
    rw [← hE]
    exact integral_re hI
  have hsq : ∀ x : HH, ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hI.re
  · rw [hfun, h2, hsq a, hsq b, ← Complex.ofReal_mul, ← Complex.ofReal_div]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    ring

theorem lintegral_hsA_sand {μ : Measure G} {σ : G → (HH →L[ℂ] HH)} {d : ℝ} (hS : IsSchur μ σ d)
    (Y : V →L[ℂ] HH) (Y' : V' →L[ℂ] HH) :
    ∫⁻ γ, ENNReal.ofReal (hsA (sand σ Y Y' γ)) ∂μ =
      ENNReal.ofReal ((∑ i, ‖Y (stdOrthonormalBasis ℂ V i)‖ ^ 2) *
        (∑ j, ‖Y' (stdOrthonormalBasis ℂ V' j)‖ ^ 2) / d) := by
  have hterm : ∀ j i,
      Integrable (fun γ => ‖⟪Y (stdOrthonormalBasis ℂ V i),
        σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2) μ ∧
      ∫ γ, ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2 ∂μ =
        ‖Y (stdOrthonormalBasis ℂ V i)‖ ^ 2 * ‖Y' (stdOrthonormalBasis ℂ V' j)‖ ^ 2 / d :=
    fun j i => schur_sq hS _ _
  have hInt : Integrable (fun γ => ∑ j, ∑ i,
      ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2) μ :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => (hterm j i).1
  have hrow : ∀ j, ∫ γ, ∑ i,
      ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2 ∂μ =
      ∑ i, ‖Y (stdOrthonormalBasis ℂ V i)‖ ^ 2 * ‖Y' (stdOrthonormalBasis ℂ V' j)‖ ^ 2 / d := by
    intro j
    rw [integral_finsetSum _ fun i _ => (hterm j i).1]
    exact Finset.sum_congr rfl fun i _ => (hterm j i).2
  have hval : ∫ γ, ∑ j, ∑ i,
      ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2 ∂μ =
      (∑ i, ‖Y (stdOrthonormalBasis ℂ V i)‖ ^ 2) *
        (∑ j, ‖Y' (stdOrthonormalBasis ℂ V' j)‖ ^ 2) / d := by
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => (hterm j i).1]
    rw [Finset.sum_congr rfl fun j _ => hrow j]
    simp only [Finset.sum_mul_sum, Finset.sum_div]
    exact Finset.sum_comm
  simp_rw [hsA_sand]
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (ae_of_all _ fun γ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _), hval]

end Formalism.L2.S.Pv.EnergyAbs
end
end

