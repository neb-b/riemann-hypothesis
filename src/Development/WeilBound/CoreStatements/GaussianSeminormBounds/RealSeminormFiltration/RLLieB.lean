module

public import Mathlib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0054
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.Bundle0002
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.EvIHalfTrace
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLines

@[expose] public section

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix Filter Topology Asymptotics
open scoped Real RealInnerProductSpace ContDiff

namespace PositivityTheory.RL.Up

open GlobalTheory.RealWeil

variable {l : Type} [Fintype l]

theorem phase_tg (w : l ⊕ l → ℝ) : (phase w).HasTemperateGrowth := by
  have h : (fun x : EuclideanSpace ℝ l => ⟪qPart w, x⟫ + ⟪pPart w, qPart w⟫ / 2).HasTemperateGrowth :=
    (innerSL ℝ (qPart w)).hasTemperateGrowth.add (Function.HasTemperateGrowth.const _)
  convert Der.chirp_tg (-1) h using 1
  funext x
  simp only [phase, Der.chirp]
  congr 1
  push_cast
  ring

def rhoS (w : l ⊕ l → ℝ) : Sch l →L[ℂ] Sch l := smulLeftCLM ℂ (phase w) ∘L compSubConstCLM ℂ (-pPart w)

theorem rhoS_apply (w : l ⊕ l → ℝ) (f : Sch l) (x : EuclideanSpace ℝ l) : rhoS w f x = phase w x * f (x + pPart w) := by
  rw [rhoS, ContinuousLinearMap.comp_apply, smulLeftCLM_apply_apply (phase_tg w)]
  simp

theorem hasDerivAt_rhoS (w : l ⊕ l → ℝ) (f : Sch l) (T : Sch l →L[ℂ] ℂ) :
    HasDerivAt (fun t : ℝ => T (rhoS (t • w) f)) (T (dRho w f)) 0 := by
  obtain ⟨G, hG, hD⟩ := Der.hl_deriv (pPart w) (-innerSL ℝ (qPart w)) f
  have e1 : ∀ t : ℝ, rhoS (t • w) f = G t := fun t => by
    ext x
    rw [hG, rhoS_apply, Der.hl, phase, pPart_smul, qPart_smul]
    congr 2
    simp only [real_inner_smul_left, real_inner_smul_right, ContinuousLinearMap.neg_apply, innerSL_apply_apply,
      real_inner_comm (pPart w) (qPart w)]
    push_cast
    ring
  have e2 : dRho w f = Der.dop (pPart w) (-innerSL ℝ (qPart w)) f := by
    ext x
    rw [dRho_apply, Der.dop_apply]
    simp
  simp only [e1, e2]
  exact hD T

theorem exists_ne : ∃ f : Sch l, f ≠ 0 := by
  let b : ContDiffBump (0 : EuclideanSpace ℝ l) := ⟨1, 2, by norm_num, by norm_num⟩
  have h1 : HasCompactSupport fun x => ((b x : ℝ) : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  refine ⟨h1.toSchwartzMap (ofRealCLM.contDiff.comp b.contDiff), fun h => ?_⟩
  have h2 : ((b 0 : ℝ) : ℂ) = 0 := congrArg (fun f : Sch l => f 0) h
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)] at h2
  simp at h2

variable [DecidableEq l]

theorem quad_eq {ι : Type} [Fintype ι] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : ι → l ⊕ l → ℝ)
    (h : ∀ w, X *ᵥ w = ∑ j, sympl (v j) w • u j) :
    quad X = (8 * π * I : ℂ)⁻¹ • ∑ j, (dRho (u j) * dRho (v j) + dRho (v j) * dRho (u j)) := by
  have hS : ∀ a b, (X * Matrix.J l ℝ) a b = ∑ j, u j a * v j b := fun a b => by
    have := congrFun (h (Matrix.J l ℝ *ᵥ Pi.single b 1)) a
    rw [mulVec_mulVec, mulVec_single_one] at this
    rw [show (X * Matrix.J l ℝ) a b = _ from this, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
    congr 1
    rcases b with b | b <;>
      simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, mulVec, dotProduct, Pi.single_apply, Matrix.one_apply]
  have e : ∀ j, dRho (u j) * dRho (v j) + dRho (v j) * dRho (u j) = ∑ a, ∑ b, ((u j a * v j b : ℝ) : ℂ) •
      (dRho (Pi.single a 1) * dRho (Pi.single b 1) + dRho (Pi.single b 1) * dRho (Pi.single a 1)) := fun j => by
    rw [dRho_eq_sum (u j), dRho_eq_sum (v j), Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := Finset.univ)
      (f := fun b a => ((v j b : ℂ) • dRho (Pi.single b 1)) * ((u j a : ℂ) • dRho (Pi.single a 1))),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, ofReal_mul]
    module
  have h8 : (8 * π * I : ℂ)⁻¹ = (4 * π * I : ℂ)⁻¹ * (1 / 2) := by
    have : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp
    norm_num
  rw [quad, h8, mul_smul]
  congr 1
  simp only [e, hS]
  rw [Finset.sum_comm (s := (Finset.univ : Finset ι)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset ι)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_smul, smul_smul]
  congr 1
  push_cast
  ring


variable (l) in
structure Meta : Type 1 where
  G : Type
  [grp : Group G]
  [top : TopologicalSpace G]
  pr : G →* Matrix.symplecticGroup l ℝ
  om : G →* (Sch l →L[ℂ] Sch l)
  quot : IsQuotientMap pr
  sgn : ∀ g, pr g = 1 → om g = 1 ∨ om g = -1
  cont : ∀ f, Continuous fun g => (om g f).toLp 2 volume
  bdd : ∀ g, ∃ L : L2 l →L[ℂ] L2 l, ∀ f, (om g f).toLp 2 volume = L (f.toLp 2 volume)
  cov : ∀ g w f, om g (rhoS w f) = rhoS ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)
  line : ∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∃ γ : ℝ → G, Continuous γ ∧ γ 0 = 1 ∧ (∀ s t, γ (s + t) = γ s * γ t) ∧
    (∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) ∧
    ∀ f : Sch l, HasDerivAt (fun t => (om (γ t) f).toLp 2 volume) ((quad X f).toLp 2 volume) 0

attribute [instance] Meta.grp Meta.top


end PositivityTheory.RL.Up

end
