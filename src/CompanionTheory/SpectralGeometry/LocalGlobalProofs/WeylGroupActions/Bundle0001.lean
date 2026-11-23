module

public import Mathlib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftAtRExistsEq
public import Formalism.HermitianCurvature.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0041
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OmgEquivariant
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0078

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.CapelliParamsDiffInt
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.GapLie

theorem capelli_params_diff_int : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (m : Fin n → ℂ), GlRel E → (∀ w v, qdet E w v = Qr.cpol m w • v) → ∀ i j, ∃ N : ℤ, m i - m j = (N : ℂ) := by
  intro V _ _ _ _ n E m hE hq
  obtain ⟨ν, v, -, hv0, hw, -⟩ := Formalism.FourierDecayAlt.P.exists_singular_maximal_vector V n E hE ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  have hc := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol (m := m) hE (Qr.mem_CapSp.2 fun w => hq w v) hv0 hw
  have hroot : ∀ i, ∃ a : Fin n, m i = ν a - ((a : ℕ) : ℂ) := by
    intro i
    have h1 := hc (-m i)
    unfold Qr.cpol at h1
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by ring)] at h1
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h1.symm
    exact ⟨a, by linear_combination -ha⟩
  have hdom : ∀ a b : Fin n, ∃ N : ℤ, ν a - ν b = (N : ℂ) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · obtain ⟨N, hN⟩ := Formalism.FourierDecayAlt.P.singular_dominant V n E ν v hE hw hv0 a b h
      exact ⟨N, by simpa using hN⟩
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨N, hN⟩ := Formalism.FourierDecayAlt.P.singular_dominant V n E ν v hE hw hv0 b a h
      refine ⟨-N, ?_⟩
      push_cast
      linear_combination -hN
  intro i j
  obtain ⟨a, ha⟩ := hroot i
  obtain ⟨b, hb⟩ := hroot j
  obtain ⟨N, hN⟩ := hdom a b
  refine ⟨N - (a : ℕ) + (b : ℕ), ?_⟩
  push_cast
  linear_combination ha - hb + hN

end GlobalTheory.CompanionTheory.GapLie
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.OmgLeftRight
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.OmgUW

lemma one_mem_UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z := by
  simp [UWset, UH]

theorem omg_left_right : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → ∀ g ∈ B.GV k r, (∀ h ∈ UWset k r z, GlobalTheory.WigSh.omg k r z z' (h * g) = GlobalTheory.WigSh.omg k r z z' (g)) ∧ ∀ h' ∈ UWset k r z', GlobalTheory.WigSh.omg k r z z' (g * h') = h'⁻¹ *ᵥ GlobalTheory.WigSh.omg k r z z' (g) := by
  intro k r z z' hz hTz hz' hTz' g hg
  refine ⟨fun h hh => ?_, fun h' hh' => ?_⟩
  · have hhU : h ∈ UH (Hpk k r) := by
      simp only [UWset, Set.mem_setOf_eq] at hh
      exact hh.1
    have hii : h⁻¹⁻¹ = h :=
      Matrix.nonsing_inv_nonsing_inv h
        (Matrix.isUnit_det_of_right_inverse (GlobalTheory.WigSh.OmgEquiv.mul_inv hhU))
    have e := GlobalTheory.WigSh.omg_equivariant k r z z' g h⁻¹ 1 hz hTz hz' hTz' hg
      (GlobalTheory.WigSh.OmgEquiv.inv_mem hh) (one_mem_UWset k r z')
    rw [hii, mul_one, inv_one, Matrix.one_mulVec] at e
    exact e
  · have e := GlobalTheory.WigSh.omg_equivariant k r z z' g 1 h' hz hTz hz' hTz' hg
      (one_mem_UWset k r z) hh'
    rw [inv_one, one_mul] at e
    exact e

end GlobalTheory.CompanionTheory.OmgUW
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.OmgNMulN
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.OmegaBiInv

theorem omg_N_mul_N : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → inWb k r z' → ∀ g ∈ B.GV k r, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, GlobalTheory.WigSh.omg k r z z' (n * g * n') = GlobalTheory.WigSh.omg k r z z' (g) := by
  intro k r z z' hz hz' g hg n hn n' hn'
  rw [Matrix.mul_assoc, GlobalTheory.WigSh.OmLeftN.omg_mul_left k r z z' (g * n') n hz hn]
  exact GlobalTheory.WigSh.omg_mul_N k r z z' g n' hz hz' hg hn'

end GlobalTheory.CompanionTheory.OmegaBiInv
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapPolynomialOperator
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.WigOmgPoly

theorem polyOp_wigMap_omg : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A → PolyOp (d * (r + 1)) (fun g : B.Mat k r => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  intro Wq _ _ Wq' _ _ k r z z' π' π'' d A hz hT hz' hT' hA
  exact (GlobalTheory.WigSh.wigMap_omg Wq Wq' k r z z' π' π'' d A hz hT hz' hT' hA).1

end GlobalTheory.CompanionTheory.WigOmgPoly
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapUpperBound
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.WigAtOmega

theorem wigUpper_omg : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type)
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ))
    (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ)
    (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)),
    inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A →
    WigUpper z z' d (fun g : B.Mat k r => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  intro Wq _ _ Wq' _ _ k r z z' π' π'' d A hz hT hz' hT' hA g hg
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.WigSh.OmgNorm.omg_norm k r z z' g hz hT hz' hT' hg
  have h := hA.2.2.2 _ h1 h2
  rw [h3] at h
  exact h

end GlobalTheory.CompanionTheory.WigAtOmega
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerPlusMinusDecomposition
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.WigLowerOmg

theorem wigLower_omg : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Wqp : Type) [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] (Wqm : Type) [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (b : ℝ) (n₀ : ℕ) (Ap : (Fin (2 * r + k + 1) → ℂ) → (Wqp →L[ℂ] Wq)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Wqm →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → (∀ ω, inWb k r ω → herm (Hpk k r) ω z' = 0 → ∀ v : Wq, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2)) → WigLower z z' b n₀ (fun g : B.Mat k r => Ap (GlobalTheory.WigSh.omg k r z z' (g))) (fun g : B.Mat k r => Am (GlobalTheory.WigSh.omg k r z z' (g))) := by
  intro Wq _ _ _ Wqp _ _ _ Wqm _ _ _ k r z z' b n₀ Ap Am hz hTz hz' hTz' hbound
  unfold WigLower
  intro g hg hGf v
  obtain ⟨hW, hperp, hre⟩ := GlobalTheory.WigSh.OmgNorm.omg_norm k r z z' g hz hTz hz' hTz' hg
  have h := hbound _ hW hperp v
  rw [hre] at h
  have hq : 0 < Gf k r z z' g / Tz k r z' := div_pos hGf hTz'
  have hqn := pow_pos hq n₀
  have key : ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) *
      (‖ContinuousLinearMap.adjoint (Ap (GlobalTheory.WigSh.omg k r z z' g)) v‖ ^ 2 +
        ‖ContinuousLinearMap.adjoint (Am (GlobalTheory.WigSh.omg k r z z' g)) v‖ ^ 2) /
      (Gf k r z z' g / Tz k r z') ^ n₀ := by
    rw [le_div_iff₀ hqn, mul_comm]
    exact h
  refine key.trans (le_of_eq ?_)
  beta_reduce
  rw [← inv_div (Gf k r z z' g) (Tz k r z'), inv_pow]
  ring

end GlobalTheory.CompanionTheory.WigLowerOmg
end

