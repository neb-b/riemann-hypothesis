module

public import Mathlib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftAtRExistsEq
public import Formalism.HermitianCurvature.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.TypeExponentsDifferByIntegers
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.GapInt

theorem type_param_diff_int : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : B.Mat k r → (Wq →L[ℂ] Wq)) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → ∀ i ∈ Finset.Icc 1 k, ∀ j ∈ Finset.Icc 1 k, ∃ N : ℤ, u i - u j = (N : ℝ) := by
  intro Wq _ _ _ k r z π u hz hT hty i hi j hj
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨Bs, hB⟩ := Formalism.FourierDecayAlt.P.Qx8.frame_exists hz hT
  obtain ⟨hnt, hrep, hcont, -, -, hcap⟩ := hty
  have hR : Qr.IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  obtain ⟨hgl, hq⟩ := Formalism.FourierDecayAlt.P.frame_general_linear Wq (n + 1) r (n + 1) z π Bs hR hB
  have hc : ∀ w v, qdet (Qr.EB π Bs) w v =
      Qr.cpol (fun a : Fin (n + 1) => (u ((a : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2) w • v := by
    intro w v
    rw [← hq w v, hcap Bs hB w v, Formalism.FourierDecayAlt.P.FrameExtension.prod_Icc_fin]
    congr 1
    unfold Qr.cpol
    refine Finset.prod_congr rfl (fun a _ => ?_)
    ring
  obtain ⟨N, hN⟩ := GlobalTheory.CompanionTheory.GapLie.capelli_params_diff_int Wq (n + 1) (Qr.EB π Bs) _ hgl hc
    ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
  refine ⟨N, ?_⟩
  have e1 : i - 1 + 1 = i := by omega
  have e2 : j - 1 + 1 = j := by omega
  simp only [e1, e2] at hN
  have h : ((u i : ℝ) : ℂ) - (u j : ℂ) = (N : ℂ) := by linear_combination hN
  exact_mod_cast h

end GlobalTheory.CompanionTheory.GapInt
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapContinuousRep
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.OmgWigEquiv

theorem wigEquiv_omg (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type)
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ))
    (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ)
    (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq))
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hz' : inWb k r z') (hT' : 0 < Tz k r z')
    (hA : GlobalTheory.WigSh.WigMap k r z' π'' π' d A) (hπ : IsCRepOn (UWset k r z') π'') :
    WigEquiv z z' π' π'' (fun g => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  refine ⟨fun g hg _ n hn n' hn' => ?_, fun g hg _ h hh => ?_, fun g hg _ h hh => ?_⟩
  · exact congrArg A (GlobalTheory.CompanionTheory.OmegaBiInv.omg_N_mul_N k r z z' hz hz' g hg n hn n' hn')
  · exact congrArg A ((GlobalTheory.CompanionTheory.OmgUW.omg_left_right k r z z' hz hT hz' hT' g hg).1 h hh)
  · have hi := Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv hh
    have h1 := (GlobalTheory.CompanionTheory.OmgUW.omg_left_right k r z z' hz hT hz' hT' g hg).2 h hh
    have h2 := hA.2.1 h⁻¹ hi (GlobalTheory.WigSh.omg k r z z' g)
    have h3 : (π'' h⁻¹).comp (π'' h) = ContinuousLinearMap.id ℂ Wq' := by
      rw [← hπ.2 _ hi _ hh, Formalism.FourierDecayAlt.P.LeftDerivativeCurves.uh_inv_mul hh.1, hπ.1]
      rfl
    show A (GlobalTheory.WigSh.omg k r z z' (g * h)) = (π' h⁻¹).comp ((A (GlobalTheory.WigSh.omg k r z z' g)).comp (π'' h))
    rw [h1, ← ContinuousLinearMap.comp_assoc, ← h2, ContinuousLinearMap.comp_assoc, h3,
      ContinuousLinearMap.comp_id]

end GlobalTheory.CompanionTheory.OmgWigEquiv
end

