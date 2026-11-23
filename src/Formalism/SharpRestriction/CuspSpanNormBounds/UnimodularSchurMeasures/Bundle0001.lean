module

public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.BesselExistenceUniformOfFacts
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ExistsTowerOfLocalSetting
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.IdempotentTranslateMeasurable
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

section Grp

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin (2 * r + k + 1) → Bool}
  {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}

theorem discrete_series_isometry (hσ : IsDSHpk k r ε lam σ) {a : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (v : H) :
    ‖σ a v‖ = ‖v‖ := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have := hDS.2.2.1.2.1 _ (cayley_conj_mem_diagonal_model hP ha).1 v
  simpa only [(cayley_conj_mem_diagonal_model hP ha).2] using this

theorem discrete_series_inner (hσ : IsDSHpk k r ε lam σ) {a : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (x y : H) :
    ⟪σ a x, σ a y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (σ a : H →ₗ[ℂ] H) (discrete_series_isometry hσ ha)).inner_map_map x y

theorem discrete_series_continuousOn (hσ : IsDSHpk k r ε lam σ) (v : H) :
    ContinuousOn (fun g => σ g v) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have h1 := hDS.2.2.1.2.2 v
  have hc : Continuous fun x : Mat k r => P * x * P⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h2 := h1.comp hc.continuousOn (fun a ha => (cayley_conj_mem_diagonal_model hP ha).1)
  refine h2.congr fun a ha => ?_
  simp only [Function.comp, (cayley_conj_mem_diagonal_model hP ha).2]

end Grp

namespace BData

variable (X : BData)

variable {X}

end BData

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionChange
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.BasicNotions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem mat_mul_mem_UH_Hpk {k r : ℕ} {g h : CayleySignature.Mat k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hh : h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : g * h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have hh' : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r := hh
  show (g * h)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * h) = Formalism.QuantumDeterminants.Hpk k r
  calc (g * h)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * h) = hᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * h := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [hg', hh']

section Move

variable {k r : ℕ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
  [InnerProductSpace ℂ H']

end Move

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SmoothVectorsTranslateUnitary
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal ContDiff
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Sm

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mat k r → (H →L[ℂ] H)}

theorem smooth_vectors_add {v1 v2 : H} (h1 : v1 ∈ smoothVecs (k := k) (r := r) σ)
    (h2 : v2 ∈ smoothVecs (k := k) (r := r) σ) : v1 + v2 ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨U1, F1, o1, m1, c1, e1⟩ := h1 g₀ hg₀
  obtain ⟨U2, F2, o2, m2, c2, e2⟩ := h2 g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => F1 g + F2 g, o1.inter o2, ⟨m1, m2⟩,
    (c1.mono Set.inter_subset_left).add (c2.mono Set.inter_subset_right), fun g hg hgU => ?_⟩
  have a1 : σ g v1 = F1 g := e1 g hg.1 hgU
  have a2 : σ g v2 = F2 g := e2 g hg.2 hgU
  show σ g (v1 + v2) = F1 g + F2 g
  rw [map_add (f := _), a1, a2]

theorem smooth_vectors_smul (c : ℂ) {v : H} (h1 : v ∈ smoothVecs (k := k) (r := r) σ) :
    c • v ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨U1, F1, o1, m1, c1, e1⟩ := h1 g₀ hg₀
  refine ⟨U1, fun g => c • F1 g, o1, m1, c1.const_smul c, fun g hg hgU => ?_⟩
  have a1 : σ g v = F1 g := e1 g hg hgU
  show σ g (c • v) = c • F1 g
  rw [map_smul, a1]

theorem smooth_vectors_translate_unitary
    (hrep : ∀ a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ (a * b) = (σ a).comp (σ b))
    {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ) {a : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    σ a v ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨U, F, o, m, c, e⟩ := hv (g₀ * a) (unitary_group_mul_mem hg₀ ha)
  have hR : ContDiff ℝ ∞ (fun x : Mat k r => x * a) :=
    (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ a)).contDiff
  refine ⟨(fun x : Mat k r => x * a) ⁻¹' U, fun x => F (x * a), o.preimage hR.continuous, m,
    c.comp hR.contDiffOn (fun x hx => hx), fun g hg hgU => ?_⟩
  have a1 : σ (g * a) v = F (g * a) := e (g * a) hg (unitary_group_mul_mem hgU ha)
  show σ g (σ a v) = F (g * a)
  rw [← a1, hrep g hgU a ha]
  rfl

end Sm

namespace BData

variable (X : BData)

variable {X}

end BData

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.UnimodF
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def RepA (X : CData) : Prop :=
  (∀ g h, X.R (g * h) = X.R g ∘L X.R h) ∧ X.R 1 = 1 ∧ (∀ g (F : X.L2), ‖X.R g F‖ = ‖F‖) ∧
    ∀ F : X.L2, Continuous fun g => X.R g F

end Formalism.MainNotions.LeviCoordinates

end
end

