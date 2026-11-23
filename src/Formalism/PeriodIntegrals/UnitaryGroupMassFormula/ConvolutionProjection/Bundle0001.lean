module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.ConvProjOf

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.SelfAdj
section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj

open PI.PhConvProj

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem inner_map_map {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (g : G) (x y : K) :
    ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let f : K →ₗᵢ[ℂ] K := ⟨(π g).toLinearMap, fun v => hπ.2.2.1 g v⟩
  exact f.inner_map_map x y

theorem map_inv_map {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (g : G) (y : K) :
    π g (π g⁻¹ y) = y := by
  have h := congrArg (fun A : K →L[ℂ] K => A y) (hπ.2.1 g g⁻¹)
  simp only [mul_inv_cancel, hπ.1, ContinuousLinearMap.coe_comp, Function.comp_apply] at h
  rw [← h]
  rfl

theorem inner_map_left {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (g : G) (x y : K) :
    ⟪π g x, y⟫_ℂ = ⟪x, π g⁻¹ y⟫_ℂ := by
  conv_lhs => rw [← (map_inv_map hπ) g y]
  exact (inner_map_map hπ) g x (π g⁻¹ y)

theorem inner_symm [MeasurableInv G] (μ : Measure G) [μ.IsInvInvariant] (ph : G → ℂ) (hph : ∀ g, ph g⁻¹ = star (ph g))
    {π : G → (K →L[ℂ] K)} (hπ : IsURep π) {T : K →L[ℂ] K} (hT : IsOpInt μ π ph T) (x y : K) :
    ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
  have h1 : ⟪T x, y⟫_ℂ = ∫ g, ph g⁻¹ * ⟪x, π g⁻¹ y⟫_ℂ ∂μ := by
    rw [← inner_conj_symm, hT y x, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_mul, inner_conj_symm, hph g]
    rw [(inner_map_left hπ)]
    rfl
  rw [h1, hT x y]
  exact integral_inv_eq_self (fun g => ph g * ⟪x, π g y⟫_ℂ) μ

theorem selfAdj : Defs.SelfAdjStep := by
  intro G _ _ _ _ _ _ μ _ _ _ ph m _ hidem K _ _ π T hπ hT x y
  exact inner_symm μ ph hidem.2.1 hπ hT x y

end PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.UrepMulApply
section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PI.UnitaryGroupMassFormula.PhConvProj.Sand

open PI.PhConvProj

section

variable {G : Type} [Group G] [TopologicalSpace G] {K : Type} [NormedAddCommGroup K]
  [InnerProductSpace ℂ K]

theorem urep_inner {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (k : G) (u v : K) :
    ⟪π k u, π k v⟫_ℂ = ⟪u, v⟫_ℂ := by
  let f : K →ₗᵢ[ℂ] K := { toLinearMap := (π k : K →ₗ[ℂ] K), norm_map' := hπ.2.2.1 k }
  exact f.inner_map_map u v

theorem urep_mul_apply {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (a b : G) (v : K) :
    π (a * b) v = π a (π b v) := by
  rw [hπ.2.1 a b]
  rfl

theorem urep_adj {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (k : G) (u v : K) :
    ⟪π k u, v⟫_ℂ = ⟪u, π k⁻¹ v⟫_ℂ := by
  have h1 : π k (π k⁻¹ v) = v := by
    rw [← urep_mul_apply hπ, mul_inv_cancel, hπ.1, ContinuousLinearMap.one_apply]
  calc ⟪π k u, v⟫_ℂ = ⟪π k u, π k (π k⁻¹ v)⟫_ℂ := by rw [h1]
    _ = ⟪u, π k⁻¹ v⟫_ℂ := urep_inner hπ k u _

end

theorem sand : Defs.SandStep := by
  intro G _ _ _ _ _ _ μ _ _ _ ph m hph hconv K _ _ π T hπ hT a
  ext y
  refine ext_inner_left ℂ (fun x => ?_)
  let F : G → ℂ := fun k => ⟪x, π k y⟫_ℂ
  have hFc : Continuous F := continuous_const.inner (hπ.2.2.2 y)
  have hFb : ∀ k, ‖F k‖ ≤ ‖x‖ * ‖y‖ := fun k =>
    (norm_inner_le_norm x (π k y)).trans_eq (by rw [hπ.2.2.1])
  have step1 : ∀ g, ⟪x, π g (π a (T y))⟫_ℂ = ∫ h, ph h * F (g * (a * h)) ∂μ := by
    intro g
    rw [← urep_mul_apply hπ, ← inv_inv (g * a), ← urep_adj hπ, hT]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only [F]
    rw [urep_adj hπ, inv_inv, ← urep_mul_apply hπ, mul_assoc]
  let A : G × G → ℂ := fun z => ph z.1 * ph z.2 * F (z.1 * (a * z.2))
  have hA : Integrable A (μ.prod μ) := by
    have h1 : Integrable (fun z : G × G => ph z.1 * ph z.2) (μ.prod μ) := hph.mul_prod hph
    have hm : AEStronglyMeasurable (fun z : G × G => F (z.1 * (a * z.2))) (μ.prod μ) :=
      (hFc.comp (continuous_fst.mul (continuous_const.mul continuous_snd))).aestronglyMeasurable
    exact h1.mul_bdd hm (Filter.Eventually.of_forall fun z => hFb _)
  have e1 : ∫ g, ph g * ∫ h, ph h * F (g * (a * h)) ∂μ ∂μ = ∫ z, A z ∂(μ.prod μ) := by
    rw [integral_prod _ hA]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [A]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only
    ring
  let Ψ : G × G → G × G := fun z => (z.1, z.1 * (a * z.2))
  have hΨ : MeasurePreserving Ψ (μ.prod μ) (μ.prod μ) :=
    (measurePreserving_prod_mul μ μ).comp ((MeasurePreserving.id μ).prod (measurePreserving_mul_left μ a))
  have hΨe : MeasurableEmbedding Ψ :=
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl G) (MeasurableEquiv.mulLeft a)).trans
      (MeasurableEquiv.shearMulRight G)).measurableEmbedding
  let B : G × G → ℂ := fun z => ph z.1 * ph (a⁻¹ * z.1⁻¹ * z.2) * F z.2
  have hBA : B ∘ Ψ = A := by
    funext z
    simp only [B, Ψ, A, Function.comp]
    have : a⁻¹ * z.1⁻¹ * (z.1 * (a * z.2)) = z.2 := by group
    rw [this]
  have hB : Integrable B (μ.prod μ) := (hΨ.integrable_comp_emb hΨe).1 (hBA ▸ hA)
  have e2 : ∫ z, A z ∂(μ.prod μ) = ∫ z, B z ∂(μ.prod μ) := by
    rw [← hBA]
    exact hΨ.integral_comp hΨe B
  show ⟪x, T (π a (T y))⟫_ℂ = ⟪x, (m a • T) y⟫_ℂ
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, hT x (π a (T y)), hT x y]
  simp_rw [step1]
  rw [e1, e2, integral_prod_symm B hB, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [B, F]
  rw [integral_mul_const, (hconv.2.2 a h).2]
  ring

end PI.UnitaryGroupMassFormula.PhConvProj.Sand
end
end

