module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.LocBCore

@[expose] public section

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section loca

variable {k r : ℕ}

lemma aps {V : Type*} [AddCommGroup V] (a b : V) : a + (b - a) = b := by
  exact add_sub_cancel a b

def Rk (k r : ℕ) (p q : Fin (2 * r + k + 1) → ℂ) : B.Mat k r := vecMulVec p (star q ᵥ* Hpk k r)

lemma Rk_mulVec (p q v : Fin (2 * r + k + 1) → ℂ) : Rk k r p q *ᵥ v = herm (Hpk k r) v q • p := by
  unfold Rk
  rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul, ← Matrix.dotProduct_mulVec]
  rfl

def Dw (k r : ℕ) : B.Mat k r := diagonal fun i => if r ≤ i.val ∧ i.val ≤ r + k then 1 else 0

lemma Dw_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Dw k r *ᵥ v = wbPart k r v := by
  funext i
  simp [Dw, Matrix.mulVec_diagonal, wbPart]

def Pm (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : B.Mat k r :=
  Dw k r + ((Tz k r z : ℂ))⁻¹ • (Rk k r z z * Dw k r)

lemma Pm_mulVec (z v : Fin (2 * r + k + 1) → ℂ) : Pm k r z *ᵥ v = prW k r z v := by
  unfold Pm
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Dw_mulVec, Rk_mulVec, smul_smul]
  unfold prW
  rw [div_eq_inv_mul]

def wv (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ) :
    Fin (r + 1) → ℂ := fun a => herm (Hpk k r) (M *ᵥ u) (fvec k r z a)

def gam (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ) :
    Fin (r + 1) → ℂ :=
  (-((Zhat k r z z' M).det)⁻¹) • ((Zhat k r z z' M).adjugate *ᵥ wv k r z M u)

def Lm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) : B.Mat k r :=
  1 + ∑ c : Fin (r + 1), ∑ a : Fin (r + 1),
    (-((Zhat k r z z' M).det)⁻¹ * (Zhat k r z z' M).adjugate c a) • (Rk k r (fvec k r z' c) (fvec k r z a) * M)

lemma Lm_mulVec (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ) :
    Lm k r z z' M *ᵥ u = u + ∑ c, gam k r z z' M u c • fvec k r z' c := by
  unfold Lm gam wv
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Rk_mulVec, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

def Phi (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) : B.Mat k r :=
  Pm k r z * M * Lm k r z z' M

lemma Phi_mulVec (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ) :
    Phi k r z z' M *ᵥ u = prW k r z (M *ᵥ (Lm k r z z' M *ᵥ u)) := by
  unfold Phi
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Pm_mulVec]

lemma s_msmul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {m : ℕ} {c : E → ℂ}
    {M : E → Matrix (Fin m) (Fin m) ℂ} (hc : Sm c s) (hM : Sm M s) : Sm (fun x => c x • M x) s :=
  sm_iff.2 fun i j => by simp only [Matrix.smul_apply, smul_eq_mul]; exact hc.mul (sm_iff.1 hM i j)

end loca

end PI.UnitaryGroupMassFormula.GsFr
