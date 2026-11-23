module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmoothTranslationMeasure.ContDiffMulRight

@[expose] public section

open Matrix
open scoped ContDiff

noncomputable section

namespace PI.PhMeasCore.UnitaryGroupMassFormula

open PI.PhMeasCore

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {Hm : Matrix (Fin n) (Fin n) ℂ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smooth_translate {w : H} (hmul : MulOnUH Hm σ) (hw : w ∈ smoothVecs Hm σ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH Hm) : σ g w ∈ smoothVecs Hm σ := by
  have hw' : PI.PhMeasCore.SmoothOnH Hm (fun x => σ x w) := hw
  show PI.PhMeasCore.SmoothOnH Hm (fun x => σ x (σ g w))
  intro g₀ hg₀
  obtain ⟨U, F, hU, hmem, hF, hFeq⟩ := hw' (g₀ * g) (mul_mem_UH (a := g₀) hg₀ hg)
  refine ⟨(fun x => x * g) ⁻¹' U, fun x => F (x * g),
    hU.preimage (contDiff_mulRight g).continuous, hmem, ?_, ?_⟩
  · exact hF.comp (contDiff_mulRight g).contDiffOn (fun x hx => hx)
  · intro x hx hxI
    have e : σ (x * g) w = F (x * g) := hFeq (x * g) hx (mul_mem_UH hxI hg)
    show σ x (σ g w) = F (x * g)
    rw [← e, hmul.2 x hxI g hg, ContinuousLinearMap.comp_apply]

end PI.PhMeasCore.UnitaryGroupMassFormula

end
