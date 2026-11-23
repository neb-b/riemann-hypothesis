module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0005
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0006

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothVectorsDiscreteSeriesGlModule
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem conj_single_comm {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) (a b c d : Fin n) :
    (Q⁻¹ * Matrix.single a b 1 * Q) * (Q⁻¹ * Matrix.single c d 1 * Q) -
      (Q⁻¹ * Matrix.single c d 1 * Q) * (Q⁻¹ * Matrix.single a b 1 * Q) =
    (if b = c then Q⁻¹ * Matrix.single a d 1 * Q else 0) -
      (if d = a then Q⁻¹ * Matrix.single c b 1 * Q else 0) := by
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ)
  have key : ∀ X Y : Matrix (Fin n) (Fin n) ℂ,
      (Q⁻¹ * X * Q) * (Q⁻¹ * Y * Q) = Q⁻¹ * (X * Y) * Q := by
    intro X Y
    calc (Q⁻¹ * X * Q) * (Q⁻¹ * Y * Q) = Q⁻¹ * X * (Q * Q⁻¹) * Y * Q := by
          simp only [Matrix.mul_assoc]
      _ = Q⁻¹ * (X * Y) * Q := by
          rw [hQQ, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  rw [key, key, ← Matrix.sub_mul, ← Matrix.mul_sub]
  by_cases hbc : b = c <;> by_cases hda : d = a
  · subst hbc hda
    simp [Matrix.single_mul_single_same, Matrix.mul_sub, Matrix.sub_mul]
  · subst hbc
    simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hda, Matrix.mul_sub, Matrix.sub_mul]
  · subst hda
    simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hbc, Matrix.mul_sub, Matrix.sub_mul]
  · simp [Matrix.single_mul_single_of_ne, hbc, hda]

theorem smooth_gl_module : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ Q : Mx k r, IsUnit Q → ∃ E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsE Q E ∧ Formalism.REAL.GlRel E := by
  intro hK k r ε mu R hR Q hQ
  obtain ⟨hsm, hlinv, hlinY, -, hcomm, -⟩ := Gp91.GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hR
  have hzero : ∀ Y : Mx k r, R.dC Y 0 = 0 := by
    intro Y
    have h := hlinv Y 1 0 R.smSub.zero_mem 0 R.smSub.zero_mem
    simpa using h
  have hY0 : ∀ v ∈ R.sm, R.dC 0 v = 0 := by
    intro v hv
    have h := hlinY 0 0 1 v hv
    simpa using h
  have hsub : ∀ Y Z : Mx k r, ∀ v ∈ R.sm, R.dC (Y - Z) v = R.dC Y v - R.dC Z v := by
    intro Y Z v hv
    have h := hlinY Z Y (-1) v hv
    rw [neg_one_smul, neg_add_eq_sub, neg_one_smul, neg_add_eq_sub] at h
    exact h
  let Em : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub := fun a b =>
    { toFun := fun v => ⟨R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v, hsm _ v v.2⟩
      map_add' := fun v w => by
        apply Subtype.ext
        have h := hlinv (Q⁻¹ * Matrix.single a b 1 * Q) 1 v v.2 w w.2
        simpa using h
      map_smul' := fun c v => by
        apply Subtype.ext
        have h := hlinv (Q⁻¹ * Matrix.single a b 1 * Q) c v v.2 0 R.smSub.zero_mem
        simpa [hzero] using h }
  have hE : ∀ a b (v : R.smSub), ((Em a b v : R.smSub) : R.H) = R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v :=
    fun _ _ _ => rfl
  refine ⟨Em, fun a b v => rfl, ?_⟩
  intro a b c d
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have hv : (v : R.H) ∈ R.sm := v.2
  have key := hcomm (Q⁻¹ * Matrix.single a b 1 * Q) (Q⁻¹ * Matrix.single c d 1 * Q) v hv
  rw [conj_single_comm Q hQ a b c d, hsub _ _ _ hv] at key
  split_ifs at key ⊢ <;>
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, hE, LinearMap.zero_apply,
      Submodule.coe_zero, sub_zero, zero_sub, hY0 _ hv] at key ⊢ <;>
    exact key

end GlobalTheory
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorWeightedBesselSumStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.tensor_weighted_bessel_sum : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (om om' : ι → ℂ) (l : R.H → Wp) (l' : R.H → Wq) (lI : ∀ I, (RI I).H → Wp) (lI' : ∀ I, (RI I).H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → IsCoef R l l' F s → ∃ (Ft : κ → Mx k r → (Wq →L[ℂ] Wp)) (st : κ → ℂ), (∀ I, IsCoef (RI I) (lI I) (lI' I) (Ft I) (st I)) ∧ (∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ om') om • F g = ∑ I, Ft I g) ∧ (∀ I, (¬ NzOn (RI I) (lI I) ∨ ¬ NzOn (RI I) (lI' I)) → st I = 0) ∧ ∀ I (κ₀ κ₁ : ℂ), (∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ • l v) → (∀ v ∈ R.sm, lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ • l' v) → st I = (ep I : ℂ) * κ₁ * star κ₀ * s := by
  first | exact @GlobalTheory.coef_mul_split | exact GlobalTheory.coef_mul_split | (intros; apply GlobalTheory.coef_mul_split <;> assumption)
end Gp91
end

