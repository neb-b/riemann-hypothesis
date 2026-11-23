module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.CutFold
section
noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Fold

theorem cutFold {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (F G : β → α → α) (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    (hmp : ∀ᵐ s ∂ν, μ.map (F s) = μ) (hinv : ∀ᵐ p ∂(ν.prod μ), G p.1 (F p.1 p.2) = p.2)
    (b : α → ℝ) (hb : Measurable b) (hb0 : ∀ x, 0 ≤ b x)
    (h1 : ∀ᵐ x ∂μ, Integrable (fun s => b (G s x)) ν ∧ ∫ s, b (G s x) ∂ν = 1)
    (φ : α → E) (hφ : Integrable φ μ) :
    Integrable (fun p : β × α => b p.2 • φ (F p.1 p.2)) (ν.prod μ) ∧
      ∫ x, φ x ∂μ = ∫ x, b x • ∫ s, φ (F s x) ∂ν ∂μ := by
  have hΦ : MeasurePreserving (fun p : β × α => (p.1, F p.1 p.2)) (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product hF hmp
  have hbG : Measurable fun q : β × α => b (G q.1 q.2) := hb.comp hG
  have hHm : AEStronglyMeasurable (fun q : β × α => b (G q.1 q.2) • φ q.2) (ν.prod μ) :=
    hbG.aestronglyMeasurable.smul hφ.1.comp_snd
  have hHi : Integrable (fun q : β × α => b (G q.1 q.2) • φ q.2) (ν.prod μ) := by
    rw [integrable_prod_iff' hHm]
    constructor
    · filter_upwards [h1] with y hy
      exact hy.1.smul_const (φ y)
    · refine hφ.norm.congr ?_
      filter_upwards [h1] with y hy
      show ‖φ y‖ = ∫ s, ‖b (G s y) • φ y‖ ∂ν
      have hn : ∀ s, ‖b (G s y) • φ y‖ = b (G s y) * ‖φ y‖ := fun s => by
        rw [norm_smul, Real.norm_of_nonneg (hb0 _)]
      simp only [hn]
      rw [integral_mul_const, hy.2, one_mul]
  have hcomp : (fun p : β × α => b p.2 • φ (F p.1 p.2)) =ᵐ[ν.prod μ]
      ((fun q : β × α => b (G q.1 q.2) • φ q.2) ∘ fun p : β × α => (p.1, F p.1 p.2)) := by
    filter_upwards [hinv] with p hp
    simp only [Function.comp_apply, hp]
  have hint : Integrable (fun p : β × α => b p.2 • φ (F p.1 p.2)) (ν.prod μ) :=
    (hΦ.integrable_comp_of_integrable hHi).congr hcomp.symm
  refine ⟨hint, ?_⟩
  have e1 : (∫ x, b x • ∫ s, φ (F s x) ∂ν ∂μ) = ∫ p, b p.2 • φ (F p.1 p.2) ∂(ν.prod μ) := by
    rw [integral_prod_symm _ hint]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact (integral_smul (b x) fun s => φ (F s x)).symm
  have hm : AEStronglyMeasurable (fun q : β × α => b (G q.1 q.2) • φ q.2)
      (Measure.map (fun p : β × α => (p.1, F p.1 p.2)) (ν.prod μ)) := by
    rw [hΦ.map_eq]
    exact hHm
  have e2 : (∫ p, b p.2 • φ (F p.1 p.2) ∂(ν.prod μ)) =
      ∫ q, b (G q.1 q.2) • φ q.2 ∂(ν.prod μ) := by
    rw [integral_congr_ae hcomp]
    calc ∫ p, ((fun q : β × α => b (G q.1 q.2) • φ q.2) ∘
            fun p : β × α => (p.1, F p.1 p.2)) p ∂(ν.prod μ)
        = ∫ q, b (G q.1 q.2) • φ q.2
            ∂(Measure.map (fun p : β × α => (p.1, F p.1 p.2)) (ν.prod μ)) :=
          (integral_map hΦ.measurable.aemeasurable hm).symm
      _ = ∫ q, b (G q.1 q.2) • φ q.2 ∂(ν.prod μ) := by rw [hΦ.map_eq]
  have e3 : (∫ q, b (G q.1 q.2) • φ q.2 ∂(ν.prod μ)) = ∫ y, φ y ∂μ := by
    rw [integral_prod_symm _ hHi]
    refine integral_congr_ae ?_
    filter_upwards [h1] with y hy
    show ∫ s, b (G s y) • φ y ∂ν = φ y
    rw [integral_smul_const, hy.2, one_smul]
  rw [e1, e2, e3]

end ReciprocityTheory.ChartRestriction.DS.Mult1.Fold
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.TransposeUnitary
section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

def RankOneMinors : Prop :=
  ∀ (X : Type) (κ : X → X → ℂ),
    (∀ x y, κ x y = star (κ y x)) → (∀ x, 0 ≤ (κ x x).re) →
    (∀ x y x' y', κ x y * κ x' y' = κ x y' * κ x' y) →
    ∃ f : X → ℂ, ∀ x y, κ x y = f x * star (f y)

def SchurDichotomy : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsInvInvariant] [μ.IsOpenPosMeasure]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (θ : G → G) (ρ : G → (H →L[ℂ] H)),
    Continuous θ → (∀ a b, θ (a * b) = θ b * θ a) → (∀ g, θ (θ g) = g) → μ.map θ = μ →
    ρ 1 = 1 → (∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) → (∀ g v, ‖ρ g v‖ = ‖v‖) →
    (∀ v, Continuous fun g => ρ g v) → (∀ v w, MemLp (fun g => ⟪w, ρ g v⟫_ℂ) 2 μ) →
    (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤) →
    (∀ x y x' y' : H, ∫ g, ⟪y, ρ (θ g) x⟫_ℂ * star ⟪y', ρ g x'⟫_ℂ ∂μ = 0) ∨
    ∃ C : H ≃ₗᵢ⋆[ℂ] H, (∀ g (x y : H), ⟪y, ρ (θ g) x⟫_ℂ = ⟪C x, ρ g (C y)⟫_ℂ) ∧
      ∀ h (v : H), C (ρ h v) = ρ (θ h)⁻¹ (C v)

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

