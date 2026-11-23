module

public import Mathlib
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep

@[expose] public section

open Module NumberField

noncomputable section

namespace Formalism.DivisionValues

theorem dual_lattice_measure :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K]
      [_root_.NumberField.IsTotallyComplex K] (D : ℕ), 0 < D →
      ∀ X : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (X v).det) →
      ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsFullLattice K R →
        Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis
          (Formalism.HN.dualFrame X) (Formalism.HN.dualLat R) = lcv X R / D := by
  intro K _ _ _ _ D hD X hX R hR
  have hFG : R.FG := hR.toIsLattice.fg
  have hsp : Submodule.span K (R : Set (Fin D → K)) = ⊤ := by
    letI : Submodule.IsFullLattice K R := hR
    exact Submodule.IsFullLattice.span_eq_top
  obtain ⟨hdFG, hdsp, -, hsize, -⟩ :=
    Formalism.HN.dual_polygon_identity K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) X hX R hFG hsp
  have hdX : ∀ v, IsUnit (Formalism.HN.dualFrame X v).det := by
    intro v
    apply Matrix.isUnit_nonsing_inv_det
    rw [Matrix.det_transpose]
    exact hX v
  have hne : Formalism.HN.dualLat R ≠ ⊥ := by
    intro h
    rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at hdsp
    have hmem : (Pi.basisFun K (Fin D)).dualBasis ⟨0, hD⟩ ∈ (⊤ : Submodule K _) := Submodule.mem_top
    rw [← hdsp, Submodule.mem_bot] at hmem
    exact (Pi.basisFun K (Fin D)).dualBasis.ne_zero _ hmem
  have hmu := (Formalism.HN.size_maximal_slope K (Module.Dual K (Fin D → K)) (Fin D) (Pi.basisFun K (Fin D)).dualBasis
    (Formalism.HN.dualFrame X) hdX (Formalism.HN.dualLat R) hdFG hne).2.1
  have hht := (Formalism.HN.place_lattice_structure K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) X hX R hFG).2.2
  have hrk : Formalism.HN.rkK R = D := by
    unfold Formalism.HN.rkK
    erw [hsp]
    simp
  have hfr := Formalism.HN.sizeMu_finrank_eq K
  have hn : (0 : ℝ) < (Formalism.HN.nPl K : ℝ) := by
    have h0 : 0 < Module.finrank ℚ K := Module.finrank_pos
    have : 0 < Formalism.HN.nPl K := by omega
    exact_mod_cast this
  have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  rw [hmu, hsize, Real.log_inv, Formalism.HN.size, Real.log_rpow hht, hrk]
  unfold Formalism.DivisionValues.lcv
  rw [hfr]
  push_cast
  field_simp

end Formalism.DivisionValues
