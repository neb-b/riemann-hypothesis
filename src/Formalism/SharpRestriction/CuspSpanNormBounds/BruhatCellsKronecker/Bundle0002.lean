module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyProjectorSectionLocal
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData

section Loc

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem umat_mem (g : Formalism.REAL.UJ ε) : umat g ∈ UJset ε := g.2

theorem continuous_umat : Continuous (fun g : Formalism.REAL.UJ ε => umat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem mul_star_eq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  have : star z = (starRingEnd ℂ) z := rfl
  rw [this, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem schur_abs {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (hd : IsFdeg (Formalism.REAL.muG ε) σ d) (x y : H) :
    Integrable (fun g : Formalism.REAL.UJ ε => ‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2) (Formalism.REAL.muG ε) ∧
      ∫ g : Formalism.REAL.UJ ε, ‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2 ∂(Formalism.REAL.muG ε) = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d := by
  obtain ⟨hi, he⟩ := hd.2 x y x y
  have hfun : (fun g : Formalism.REAL.UJ ε => coefOn σ x y g * star (coefOn σ x y g)) =
      fun g : Formalism.REAL.UJ ε => ((‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    exact mul_star_eq _
  rw [hfun] at hi he
  refine ⟨?_, ?_⟩
  · exact hi.re.congr (Filter.Eventually.of_forall fun g => Complex.ofReal_re _)
  · rw [integral_complex_ofReal] at he
    have h2 : ((∫ g : Formalism.REAL.UJ ε, ‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2 ∂(Formalism.REAL.muG ε) : ℝ) : ℂ) =
        ((‖x‖ ^ 2 * ‖y‖ ^ 2 / d : ℝ) : ℂ) := by
      rw [he, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    exact_mod_cast h2

theorem fdegOf_eq {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (hd : IsFdeg (Formalism.REAL.muG ε) σ d) {w : H} (hw : ‖w‖ = 1) : fdegOf (Formalism.REAL.muG ε) σ w = d := by
  unfold fdegOf
  have h := (schur_abs hd w w).2
  have h' : ∫ g : Formalism.REAL.UJ ε, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 1 / d := by
    have : (fun g : Formalism.REAL.UJ ε => ‖coefOn σ w w g‖ ^ 2) = fun g : Formalism.REAL.UJ ε => ‖⟪w, σ (umat g) w⟫_ℂ‖ ^ 2 := rfl
    rw [this, h, hw]
    norm_num
  rw [h', hw]
  have := hd.1
  field_simp

end Loc

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionConvolutionIdentity
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory
open scoped InnerProductSpace ComplexOrder ENNReal

section Abs

variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G)

theorem inv_invariant_of_bi_invariant [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsOpenPosMeasure] [SigmaFinite μ]
    (f : G → ℝ) (hf : Continuous f) (hi : Integrable f μ) (h1 : 0 < f 1) : μ.IsInvInvariant := by
  open scoped Pointwise in
    have hUo : IsOpen {h : G | f 1 / 2 < f h} := isOpen_lt continuous_const hf
    have h1U : (1 : G) ∈ {h : G | f 1 / 2 < f h} := by
      show f 1 / 2 < f 1
      linarith
    have hUfin : μ {h : G | f 1 / 2 < f h} < ⊤ := by
      refine lt_of_le_of_lt (measure_mono fun h hh => ?_) (hi.measure_norm_ge_lt_top (half_pos h1))
      have hh' : f 1 / 2 < f h := hh
      show f 1 / 2 ≤ ‖f h‖
      rw [Real.norm_eq_abs]
      exact hh'.le.trans (le_abs_self _)
    have hso : IsOpen ({h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹) := hUo.inter hUo.inv
    have hs1 : (1 : G) ∈ {h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹ :=
      ⟨h1U, by rw [Set.mem_inv, inv_one]; exact h1U⟩
    have hsinv : ({h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹)⁻¹ =
        {h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹ := by
      rw [Set.inter_inv, inv_inv, Set.inter_comm]
    have hs0 : μ ({h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹) ≠ 0 :=
      hso.measure_ne_zero μ ⟨1, hs1⟩
    have hstop : μ ({h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹) ≠ ⊤ :=
      (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hUfin).ne
    have key := measure_eq_div_smul μ.inv μ hs0 hstop
    rw [Measure.inv_apply, hsinv, ENNReal.div_self hs0 hstop, one_smul] at key
    exact ⟨key⟩

open Formalism.MainNotions.PlaceDegreeData (phA IsOpIntA)

variable {Hp : Type} [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]

end Abs

end Formalism.MainNotions.BridgeLemma

end
end

