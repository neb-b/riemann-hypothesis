module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HSClosing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqZeroOfSecTraceMulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.FderivFderivLogRho
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FSLevi

variable {J : Type} [Fintype J]

def reP (p : J) : (J → ℂ) →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj p)

def imaginary (p : J) : (J → ℂ) →L[ℝ] ℝ := Complex.imCLM.comp (ContinuousLinearMap.proj p)

def nsq (z : J → ℂ) : ℝ := ∑ p, (reP p z ^ 2 + imaginary p z ^ 2)

theorem reP_apply (p : J) (z : J → ℂ) : reP p z = (z p).re := rfl

theorem imaginaryPart_apply (p : J) (z : J → ℂ) : imaginary p z = (z p).im := rfl

theorem norm_sq_eq (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem nsq_pos {z : J → ℂ} (hz : z ≠ 0) : 0 < nsq z := by
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hz
  refine Finset.sum_pos' (fun q _ ↦ by positivity) ⟨p, Finset.mem_univ _, ?_⟩
  rw [reP_apply, imaginaryPart_apply, ← norm_sq_eq]
  exact pow_pos (norm_pos_iff.mpr hp) 2

end FSLevi

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertDimZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem mixedDiff_zero {K : Type*} (h : (K → ℤ) → ℤ) (bs : Fin 0 → K → ℤ) :
    mixedDiff bs h = h := by
  simp [mixedDiff]

theorem relDim_eq_zero_of_ringKrullDim {F : Type*} [Field F] {K : Type} [Fintype K]
    {ι : K → Type} (q : Ideal (MRing ι F))
    (hd : ringKrullDim (MRing ι F ⧸ q) = ((Fintype.card K : ℕ) : WithBot ℕ∞)) :
    GroundTheory.Heights₂.Heights.FieldNumbers.relDim q = ((0 : ℕ) : WithBot (WithTop ℤ)) := by
  unfold GroundTheory.Heights₂.Heights.FieldNumbers.relDim
  rw [hd]
  simp
  change WithTop.map (fun e : ℕ => (e : ℤ) - (Fintype.card K : ℤ))
    ((Fintype.card K : ℕ) : WithTop ℕ) = 0
  exact congrArg WithTop.some (sub_self _)

theorem HilbertDimZero.proof : HilbertDimZero.Statement.{u} := by
  intro F _ K _ _ ι _ q hq hd
  have h0 := ((GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst.full.{u} F K ι q hq.multiHomog
    hq.relevant 0 (relDim_eq_zero_of_ringKrullDim q hd)).1 (![] : Fin 0 → K → ℤ))
  simp only [mixedDiff_zero] at h0
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 h0
  refine ⟨Finset.univ.sup fun k => (b k).toNat, fun a ha => hb _ fun k => ?_⟩
  have h1 : (b k).toNat ≤ a k :=
    le_trans (Finset.le_sup (f := fun k => (b k).toNat) (Finset.mem_univ k)) (ha k)
  have h2 : b k ≤ ((b k).toNat : ℤ) := Int.self_le_toNat (b k)
  show b k ≤ (a k : ℤ)
  omega

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

