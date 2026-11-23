module

public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0009
public import GroundTheory.AutomorphicForms.Bundle0006
public import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract

@[expose] public section

open MeasureTheory Topology Filter Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] (Γ : Subgroup G)

def automorphicKernel (f : CompactlySupportedContinuousMap G ℂ) (p : G × G) : ℂ :=
  ∑ᶠ γ : Γ, f (p.1⁻¹ * γ * p.2)

theorem automorphicKernel_smul_left (f : CompactlySupportedContinuousMap G ℂ) (δ : Γ) (a b : G) :
    automorphicKernel Γ f (δ • a, b) = automorphicKernel Γ f (a, b) := by
  unfold automorphicKernel
  rw [← finsum_comp_equiv (Equiv.mulLeft δ)]
  refine finsum_congr fun γ => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul]
  congr 1
  group

theorem automorphicKernel_smul_right (f : CompactlySupportedContinuousMap G ℂ) (δ : Γ) (a b : G) :
    automorphicKernel Γ f (a, δ • b) = automorphicKernel Γ f (a, b) := by
  unfold automorphicKernel
  rw [← finsum_comp_equiv (Equiv.mulRight δ⁻¹)]
  refine finsum_congr fun γ => ?_
  simp only [Equiv.coe_mulRight, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul,
    Subgroup.coe_inv]
  congr 1
  group

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [DiscreteTopology Γ]

theorem locallyFinite_support_automorphicKernel (f : CompactlySupportedContinuousMap G ℂ) :
    LocallyFinite fun γ : Γ => support fun p : G × G => f (p.1⁻¹ * γ * p.2) := by
  intro p
  obtain ⟨A, hAc, hA⟩ := exists_compact_mem_nhds p.1
  obtain ⟨B, hBc, hB⟩ := exists_compact_mem_nhds p.2
  refine ⟨A ×ˢ B, prod_mem_nhds hA hB, ?_⟩
  have hAS : IsCompact (A * tsupport f) := hAc.mul f.hasCompactSupport
  refine (ProperlyDiscontinuousSMul.finite_disjoint_inter_image hBc hAS).subset ?_
  rintro γ ⟨⟨a, b⟩, hq, hab⟩
  simp only [mem_prod] at hab
  refine ⟨γ • b, mem_image_of_mem _ hab.2, ?_⟩
  refine ⟨a, hab.1, a⁻¹ * γ * b, subset_tsupport _ hq, ?_⟩
  rw [Subgroup.smul_def, smul_eq_mul]
  group

theorem continuous_automorphicKernel (f : CompactlySupportedContinuousMap G ℂ) :
    Continuous (automorphicKernel Γ f) :=
  continuous_finsum (fun γ => f.continuous.comp (by fun_prop))
    (locallyFinite_support_automorphicKernel Γ f)

theorem finite_support_automorphicKernel (f : CompactlySupportedContinuousMap G ℂ) (p : G × G) :
    (support fun γ : Γ => f (p.1⁻¹ * γ * p.2)).Finite := by
  exact (locallyFinite_support_automorphicKernel Γ f).point_finite p

def quotientKernel (f : CompactlySupportedContinuousMap G ℂ)
    (p : RightCosetSpace Γ × RightCosetSpace Γ) : ℂ :=
  Quotient.lift₂ (fun a b => automorphicKernel Γ f (a, b)) (fun a₁ b₁ a₂ b₂ ha hb => by
    obtain ⟨δ, rfl⟩ := ha
    obtain ⟨ε, rfl⟩ := hb
    rw [automorphicKernel_smul_left, automorphicKernel_smul_right]) p.1 p.2

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [DiscreteTopology Γ] in
@[simp] theorem quotientKernel_mk (f : CompactlySupportedContinuousMap G ℂ) (a b : G) :
    quotientKernel Γ f (mk Γ a, mk Γ b) = ∑ᶠ γ : Γ, f (a⁻¹ * γ * b) :=
  rfl

theorem continuous_quotientKernel (f : CompactlySupportedContinuousMap G ℂ) :
    Continuous (quotientKernel Γ f) := by
  have hq : IsQuotientMap (Prod.map (mk Γ) (mk Γ)) :=
    ((isOpenQuotientMap_mk Γ).prodMap (isOpenQuotientMap_mk Γ)).isQuotientMap
  refine hq.continuous_iff.2 ?_
  exact continuous_automorphicKernel Γ f

section Operator

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ]

def rightRegularRep : UnitaryRep G (Lp ℂ 2 (quotientMeasure Γ μ)) :=
  UnitaryRep.ofLinearIsometryEquiv (rightRegular Γ μ) (continuous_rightRegular_apply Γ μ)

theorem rightRegularRep_apply (g : G) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    rightRegularRep Γ μ g φ = rightTranslate Γ μ g φ :=
  rfl

theorem coeFn_rightRegularRep (g : G) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    rightRegularRep Γ μ g φ =ᵐ[quotientMeasure Γ μ] fun x => φ (rightMul Γ g x) :=
  coeFn_rightTranslate Γ μ g φ


variable [CompactSpace (RightCosetSpace Γ)]


omit [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] in
theorem coeFn_compactSupportToL1 (f : CompactlySupportedContinuousMap G ℂ) :
    (UnitaryRep.ccToL1 μ f : G → ℂ) =ᵐ[μ] f :=
  MemLp.coeFn_toLp _



end Operator

end RightCosetSpace

end

end GroundTheory.Automorphic
