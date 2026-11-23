module

public import Formalism.RealPlaceAnalysis.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
public import Mathlib
public import Formalism.RealPlaceAnalysis.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0065
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0005
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0002

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InverseGramEigenvaluesSumHsStatement
section
open Matrix ReciprocityTheory.ChartRestriction.DS

open scoped ComplexOrder in
theorem GlobalTheory.T.inverse_gram_eigenvalues_sum_hs (n : ℕ) (ε : Fin n → Bool) (g : S7.UJ ε)
    (hT : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).IsHermitian) :
    (∀ i, 0 < hT.eigenvalues i) ∧ ∑ i, hT.eigenvalues i = Formalism.REAL.hs (S7.toM g) := by
  have hmul : S7.toM g * S7.toM g⁻¹ = 1 := by
    show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      ((g⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = 1
    simp
  have hinj : Function.Injective (S7.toM g⁻¹).mulVec := by
    intro x y hxy
    have h := congrArg (S7.toM g).mulVec hxy
    simpa [Matrix.mulVec_mulVec, hmul] using h
  have hpd : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self _ hinj
  refine ⟨fun i => hpd.eigenvalues_pos i, ?_⟩
  have hre : ∑ i, hT.eigenvalues i = (Matrix.trace ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹)).re := by
    simpa only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] using
      (congrArg Complex.re hT.trace_eq_sum_eigenvalues).symm
  have hs_ct (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs Mᴴ = Formalism.REAL.hs M := by
    delta Formalism.REAL.hs
    simp only [Matrix.conjTranspose_apply, norm_star]
    exact Finset.sum_comm
  have hs_j_left (M : Matrix (Fin n) (Fin n) ℂ) :
      Formalism.REAL.hs (Formalism.REAL.Jm ε * M) = Formalism.REAL.hs M := by
    have h : ∀ a, ‖(if ε a = true then (1 : ℂ) else -1)‖ = 1 := fun a => by split_ifs <;> simp
    delta Formalism.REAL.hs Formalism.REAL.Jm
    simp only [Matrix.diagonal_mul, norm_mul, h, one_mul]
  have hs_j_right (M : Matrix (Fin n) (Fin n) ℂ) :
      Formalism.REAL.hs (M * Formalism.REAL.Jm ε) = Formalism.REAL.hs M := by
    rw [← hs_ct, conjTranspose_mul, Formalism.REAL.Jm_conjTranspose, hs_j_left, hs_ct]
  have hhs : Formalism.REAL.hs (S7.toM g⁻¹) = Formalism.REAL.hs (S7.toM g) := by
    rw [S7.toM_inv]
    show Formalism.REAL.hs (Formalism.REAL.Jm ε * (S7.toM g)ᴴ * Formalism.REAL.Jm ε) = _
    rw [hs_j_right, hs_j_left, hs_ct]
  rw [hre, ← Formalism.REAL.f1auxiliary_hs_eq, hhs]

theorem GlobalTheory.CompanionTheory.UGeo.specpos_inv_eigenvalues (n : ℕ) (ε : Fin n → Bool)
    (g : S7.UJ ε) (hT : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).IsHermitian) :
    (∀ i, 0 < hT.eigenvalues i) ∧ ∑ i, hT.eigenvalues i = Formalism.REAL.hs (S7.toM g) :=
  GlobalTheory.T.inverse_gram_eigenvalues_sum_hs n ε g hT
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantEquality
section
open Formalism.REAL ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

namespace GlobalTheory.CompanionTheory.RgExhHecke

theorem capEntry_eq_Tm {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (x : ℂ) (a b : Fin n) : capEntry E x a b = Tm E x a b := by
  unfold capEntry Tm
  exact add_comm _ _

theorem qdet_eq_capelliC {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (x : ℂ) : qdet E x = capelliC E x := by
  unfold qdet qminor capelliC cminor
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [capEntry_eq_Tm, zsmul_eq_mul]

theorem qdetEq : ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (x : ℂ), qdet E x = capelliC E x :=
  fun _ _ _ _ E x => qdet_eq_capelliC E x

end GlobalTheory.CompanionTheory.RgExhHecke
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ShuffleOfPermImports
section

end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugationPreservesCongruenceStatement
section
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_conjugation_preserves_congruence : ∀ {L E ι : Type} [NormedField L] [Ring E] [Algebra L E] [Fintype ι] (wt : ι → ℕ) (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ J : AddSubgroup E, GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P → (∀ c : L, ‖c‖ ≤ 1 → ∀ x ∈ J, c • x ∈ J) → ∀ (T T' : E) (τ : ι → L), (∀ i, τ i ≠ 0) → T * T' = 1 → T' * T = 1 → (∀ i, T * P i = τ i • P i) → (∀ i, P i * T = τ i • P i) → (∀ i j, wt i ≤ wt j → ‖τ i‖ ≤ ‖τ j‖) → ∀ a b : E, a - 1 ∈ J → b - 1 ∈ J → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b → T * a * T' - 1 ∈ J ∧ T' * b * T - 1 ∈ J := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.TorusConj.conj_congruence | exact GlobalTheory.CompanionTheory.Iwahori.TorusConj.conj_congruence | (intros; apply GlobalTheory.CompanionTheory.Iwahori.TorusConj.conj_congruence <;> assumption)
end

