module

public import Mathlib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftAtRExistsEq
public import Formalism.HermitianCurvature.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.Bundle0002

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.TypeExponentsConsecutiveGap
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.TypeGaps

theorem gap_eq_nat_add_one :
    ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : B.Mat k r → (Wq →L[ℂ] Wq)) (u : ℕ → ℝ),
      inWb k r z → 0 < Tz k r z → IsType k r z π u →
      (∀ i ∈ Finset.Ico 1 k, u (i + 1) + 1 ≤ u i) →
      ∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1 := by
  intro Wq _ _ _ k r z π u hz hT hty hdec i hi
  rw [Finset.mem_Icc] at hi
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.CompanionTheory.GapInt.type_param_diff_int Wq k r z π u hz hT hty i
    (Finset.mem_Icc.2 ⟨hi.1, by omega⟩) (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have h1 := hdec i (Finset.mem_Ico.2 ⟨hi.1, by omega⟩)
  have h2 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have h3 : (1 : ℤ) ≤ N := by exact_mod_cast h2
  refine ⟨(N - 1).toNat, ?_⟩
  have h4 : (((N - 1).toNat : ℕ) : ℤ) = N - 1 := Int.toNat_of_nonneg (by omega)
  have h5 : (((N - 1).toNat : ℕ) : ℝ) = (N : ℝ) - 1 := by exact_mod_cast h4
  rw [hN, h5]
  ring

end GlobalTheory.CompanionTheory.TypeGaps
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapContinuousRepStatement
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wigEquiv_of_wigMap_of_isCRepOn : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A → IsCRepOn (UWset k r z') π'' → WigEquiv z z' π' π'' (fun g => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  first | exact @GlobalTheory.CompanionTheory.OmgWigEquiv.wigEquiv_omg | exact GlobalTheory.CompanionTheory.OmgWigEquiv.wigEquiv_omg | (intros; apply GlobalTheory.CompanionTheory.OmgWigEquiv.wigEquiv_omg <;> assumption)
end

