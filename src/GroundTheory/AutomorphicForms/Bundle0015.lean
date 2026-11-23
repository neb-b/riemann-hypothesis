module

public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0012
public import GroundTheory.AutomorphicForms.DixmierMalliavinLine
public import GroundTheory.AutomorphicForms.Bundle0014
public import GroundTheory.AutomorphicForms.HeckeAlgebra
public import GroundTheory.AutomorphicForms.QuotientKernel
public import GroundTheory.AutomorphicForms.Bundle0006
public import GroundTheory.AutomorphicForms.Bundle0007

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.DixmierMalliavin
section
namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

theorem exists_decomp_direction {f : G → ℂ}
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f)
    (hfc : HasCompactSupport f) (X : 𝔤) {ε : ℝ} (hε : 0 < ε) :
    ∃ f₁ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f₁) ∧
      HasCompactSupport f₁ ∧
      ∃ g k : ℝ → ℂ, ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ k ∧ tsupport g ⊆ Icc (-ε) ε ∧
        tsupport k ⊆ Icc (-ε) ε ∧
        ∀ x, f x = (∫ t, g t * f₁ (h.expG (t • X) * x)) + ∫ t, k t * f (h.expG (t • X) * x) := by
  obtain ⟨M, hM, hser⟩ := h.exists_bound_dirDeriv hf hfc X
  obtain ⟨c, g, k, hg, hk, hgs, hks, hc, hid⟩ := exists_dixmierMalliavin_line M hε
  obtain ⟨hf₁, hf₁c⟩ := hser c hc
  refine ⟨_, hf₁, hf₁c, g, k, hg, hk, hgs, hks, fun x => ?_⟩
  set F : ℝ → ℂ := fun t => f (h.expG (t • X) * x) with hFdef
  have hF : ContDiff ℝ ∞ F := h.contDiff_comp_expG_smul_mul hf X x
  have hD : ∀ p t, iteratedDeriv p F t = h.dirDeriv X p f (h.expG (t • X) * x) :=
    fun p t => h.iteratedDeriv_comp_expG_mul X p f x t
  have key := hid F hF (fun p t _ => by rw [hD]; exact hM p _)
  have hF0 : F 0 = f x := by
    simp only [hFdef, zero_smul]; rw [h.expG_zero, one_mul]
  rw [hF0] at key
  rw [key]
  congr 1
  · have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
    have hcont : ∀ p, Continuous (fun t => iteratedDeriv p F t) := fun p =>
      hF.continuous_iteratedDeriv p (by exact_mod_cast le_top)
    let T : ℕ → ℝ → ℂ := fun p t => (c p : ℂ) * (iteratedDeriv p F t * g t)
    have hTi : ∀ p, Integrable (T p) := fun p =>
      (((hcont p).mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left).const_mul _
    have hTb : ∀ p t, ‖T p t‖ ≤ |c p| * M p * ‖g t‖ := by
      intro p t
      simp only [T, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [mul_assoc (|c p|)]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg (c p))
      have : ‖iteratedDeriv p F t‖ ≤ M p := by rw [hD]; exact hM p _
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have hgi : Integrable (fun t => ‖g t‖) :=
      (hg.continuous.integrable_of_hasCompactSupport hgc).norm
    have hsum : Summable fun p => ∫ t, ‖T p t‖ := by
      refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _)
        (fun p => ?_) (hc.mul_right (∫ t, ‖g t‖))
      rw [← integral_const_mul]
      exact integral_mono (hTi p).norm (hgi.const_mul _) (fun t => hTb p t)
    have e1 : ∀ p, (c p : ℂ) * ∫ t, iteratedDeriv p F t * g t = ∫ t, T p t := fun p =>
      (integral_const_mul _ _).symm
    simp_rw [e1]
    rw [integral_tsum_of_summable_integral_norm hTi hsum]
    congr 1
    funext t
    rw [← tsum_mul_left]
    congr 1
    funext p
    simp only [T, hD]
    ring
  · congr 1; funext t; rw [mul_comm]

theorem exists_decomp_iter {ε : ℝ} (hε : 0 < ε) : ∀ {d : ℕ} (X : Fin d → 𝔤) (f : G → ℂ),
    (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) → HasCompactSupport f →
    ∃ (m : ℕ) (F : Fin m → G → ℂ) (K : Fin m → (Fin d → ℝ) → ℂ),
      (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (F i)) ∧
        HasCompactSupport (F i)) ∧
      (∀ i, ContDiff ℝ ∞ (K i) ∧ tsupport (K i) ⊆ Metric.closedBall 0 ε) ∧
      ∀ x, f x = ∑ i, ∫ t, K i t * F i (h.revProdExp X t * x) := by
  intro d
  induction d with
  | zero =>
    intro X f hf hfc
    refine ⟨1, fun _ => f, fun _ _ => 1, fun _ => ⟨hf, hfc⟩, fun _ => ⟨contDiff_const, ?_⟩,
      fun x => ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]; exact Metric.mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      simp only [h.revProdExp_zero, one_mul, integral_const, hv, one_smul, Fin.sum_univ_one]
  | succ d ih =>
    intro X f hf hfc
    let := h.chartedSpace
    obtain ⟨f₁, hf₁, hf₁c, g, k, hg, hk, hgs, hks, hdec⟩ :=
      h.exists_decomp_direction hf hfc (X 0) hε
    obtain ⟨m₁, F₁, K₁, hF₁, hK₁, hd₁⟩ := ih (Fin.tail X) f₁ hf₁ hf₁c
    obtain ⟨m₂, F₂, K₂, hF₂, hK₂, hd₂⟩ := ih (Fin.tail X) f hf hfc
    refine ⟨m₁ + m₂, Fin.append F₁ F₂,
      Fin.append (fun i t => g (t 0) * K₁ i (Fin.tail t)) (fun i t => k (t 0) * K₂ i (Fin.tail t)),
      ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using hF₁ i
      · simpa only [Fin.append_right] using hF₂ i
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        exact ⟨contDiff_cons_kernel hg (hK₁ i).1, tsupport_cons_kernel hε.le hgs (hK₁ i).2⟩
      · simp only [Fin.append_right]
        exact ⟨contDiff_cons_kernel hk (hK₂ i).1, tsupport_cons_kernel hε.le hks (hK₂ i).2⟩
    · intro x
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hdec x]
      congr 1
      · exact (h.sum_integral_cons_kernel X hε.le hg.continuous hgs (fun i => (hK₁ i).1.continuous)
          (fun i => (hK₁ i).2) (fun i => (hF₁ i).1.continuous) hd₁ x).symm
      · exact (h.sum_integral_cons_kernel X hε.le hk.continuous hks (fun i => (hK₂ i).1.continuous)
          (fun i => (hK₂ i).2) (fun i => (hF₂ i).1.continuous) hd₂ x).symm

end IsExpLieAlgebra

theorem dixmierMalliavin (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (f : G → ℂ)
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (hfc : HasCompactSupport f) :
    ∃ (n : ℕ) (φ ψ : Fin n → G → ℂ),
      (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (φ i)) ∧
        HasCompactSupport (φ i) ∧
        (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (ψ i)) ∧ HasCompactSupport (ψ i)) ∧
      f = ∑ i, groupConv μ (φ i) (ψ i) := by
  let := h.chartedSpace
  let b := Module.finBasis ℝ 𝔤
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_prodExp μ b
  obtain ⟨m, F, K, hF, hK, hd⟩ := h.exists_decomp_iter hε (⇑b) f hf hfc
  have hK' : ∀ i, ContDiff ℝ ∞ (fun t => K i (-t)) ∧
      tsupport (fun t => K i (-t)) ⊆ Metric.closedBall 0 ε := by
    intro i
    refine ⟨(hK i).1.comp contDiff_neg, ?_⟩
    intro t ht
    have : -t ∈ tsupport (K i) := by
      have := tsupport_comp_subset_preimage (K i) (f := fun t : Fin _ → ℝ => -t) continuous_neg ht
      simpa using this
    have := (hK i).2 this
    simpa [mem_closedBall_zero_iff, norm_neg] using this
  choose κ hκs hκc hκ using fun i => hdens (fun t => K i (-t)) (hK' i).1 (hK' i).2
  refine ⟨m, κ, F, fun i => ⟨hκs i, hκc i, (hF i).1, (hF i).2⟩, ?_⟩
  funext x
  rw [hd x, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [groupConv, hκ i (fun y => F i (y⁻¹ * x))
    ((hF i).1.continuous.comp (continuous_inv.mul continuous_const))]
  have e : ∀ t : Fin (Module.finrank ℝ 𝔤) → ℝ, K i (-t) * F i ((h.prodExp (⇑b) t)⁻¹ * x) =
      (fun s => K i s * F i (h.revProdExp (⇑b) s * x)) (-t) := by
    intro t
    have := h.revProdExp_inv (⇑b) (-t)
    rw [neg_neg] at this
    simp only [← this, inv_inv]
  simp_rw [e]
  exact (integral_neg_eq_self (fun s => K i s * F i (h.revProdExp (⇑b) s * x)) volume).symm

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.TraceFormulaConvolution
section
open MeasureTheory Topology Filter Set Function
open scoped ENNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

section Convolution

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G)

def convFun (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) (x : G) : ℂ :=
  ∫ g, f₁ g * f₂ (g⁻¹ * x) ∂μ

theorem convFun_eq_setIntegral (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) (x : G) :
    convFun μ f₁ f₂ x = ∫ g in tsupport f₁, f₁ g * f₂ (g⁻¹ * x) ∂μ := by
  rw [convFun, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro g hg
  rw [image_eq_zero_of_notMem_tsupport hg, zero_mul]

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G] [IsFiniteMeasureOnCompacts μ] in
theorem continuous_convFun (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) :
    Continuous (convFun μ f₁ f₂) := by
  have h : convFun μ f₁ f₂ = fun x => ∫ g in tsupport f₁, f₁ g * f₂ (g⁻¹ * x) ∂μ :=
    funext (convFun_eq_setIntegral μ f₁ f₂)
  rw [h]
  exact continuous_parametric_integral_of_continuous (f := fun x g => f₁ g * f₂ (g⁻¹ * x))
    (by fun_prop) f₁.hasCompactSupport

theorem convFun_eq_zero (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) {x : G}
    (hx : x ∉ tsupport f₁ * tsupport f₂) : convFun μ f₁ f₂ x = 0 := by
  rw [convFun]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun g => ?_)
  by_cases h1 : g ∈ tsupport f₁
  · have h2 : g⁻¹ * x ∉ tsupport f₂ := fun h2 =>
      hx ⟨g, h1, g⁻¹ * x, h2, by simp only [mul_inv_cancel_left]⟩
    simp [image_eq_zero_of_notMem_tsupport h2]
  · simp [image_eq_zero_of_notMem_tsupport h1]

variable [IsTopologicalGroup G] [T2Space G] in
theorem hasCompactSupport_convFun (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) :
    HasCompactSupport (convFun μ f₁ f₂) :=
  HasCompactSupport.intro (f₁.hasCompactSupport.mul f₂.hasCompactSupport)
    fun _ hx => convFun_eq_zero μ f₁ f₂ hx

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
  [BorelSpace G] [IsFiniteMeasureOnCompacts μ]

def conv (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) : CompactlySupportedContinuousMap G ℂ where
  toFun := convFun μ f₁ f₂
  continuous_toFun := continuous_convFun μ f₁ f₂
  hasCompactSupport' := hasCompactSupport_convFun μ f₁ f₂

theorem conv_apply (f₁ f₂ : CompactlySupportedContinuousMap G ℂ) (x : G) :
    conv μ f₁ f₂ x = ∫ g, f₁ g * f₂ (g⁻¹ * x) ∂μ :=
  rfl

end Convolution

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ]


omit [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] in
theorem finite_setOf_mem_of_isCompact [IsTopologicalGroup G] {C : Set G} (hC : IsCompact C) :
    {δ : Γ | (δ : G) ∈ C}.Finite := by
  have hcl : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discrete
  exact (hcl.isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage hC).finite_of_discrete

section Kernel

variable (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]

variable [CompactSpace (RightCosetSpace Γ)]

end Kernel

section Operator

variable (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ]
  [CompactSpace (RightCosetSpace Γ)]

end Operator

end RightCosetSpace

section TotallyDisconnected

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

variable (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]

variable [TotallyDisconnectedSpace G]

end TotallyDisconnected

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [TotallyDisconnectedSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (RightCosetSpace Γ)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

end RightCosetSpace

end

end GroundTheory.Automorphic
end

