module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ReproCoreStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.OrbitIntegralAbsConvergent

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.HpkMulVecMulVec
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.Core

open Formalism.QuantumDeterminants

section hpk

variable (k r : ℕ)

theorem hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  have key : ∀ (c : ℕ) (hc : c < 2 * r + k + 1) (a : ℂ),
      ∑ j : Fin (2 * r + k + 1), (if j.val = c then a else 0) * v j = a * v ⟨c, hc⟩ := by
    intro c hc a
    rw [Finset.sum_eq_single ⟨c, hc⟩]
    · simp
    · intro b _ hb
      have hbc : b.val ≠ c := fun h => hb (Fin.ext h)
      simp [hbc]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hi := i.isLt
  simp only [Matrix.mulVec, dotProduct]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h]
    simp only [hpk_out k r h]
    rw [key _ (by omega), one_mul]
  · rw [if_neg h]
    simp only [hpk_mid k r h]
    rw [key i.val hi]
    split_ifs <;> simp

theorem hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i
  have hi := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · have h' : (2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val) := by omega
    rw [hpk_mulVec, if_pos h, hpk_mulVec, if_pos h']
    congr 1
    ext
    simp only
    omega
  · rw [hpk_mulVec, if_neg h, hpk_mulVec, if_neg h]
    split_ifs <;> simp

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Matrix.mulVec_mulVec, hpk_mulVec_mulVec, Matrix.one_mulVec]

end hpk

theorem inv_mul_UH (k r : ℕ) {g : Mat k r} (hg : g ∈ UH (Hpk k r)) :
    Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r * Hpk k r := by rw [hg']
    _ = 1 := hpk_sq k r

theorem mul_inv_UH (k r : ℕ) {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 := by
  have h := inv_mul_UH k r hg
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse h)

theorem mul_mem_UH (k r : ℕ) {g x : Mat k r} (hg : g ∈ UH (Hpk k r)) (hx : x ∈ UH (Hpk k r)) :
    g * x ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  show (g * x)ᴴ * Hpk k r * (g * x) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc xᴴ * gᴴ * Hpk k r * (g * x) = xᴴ * (gᴴ * Hpk k r * g) * x := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hx']

theorem inv_mem_UH (k r : ℕ) (g : Mat k r) (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have e := mul_inv_UH k r hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [e]; simp

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.Core
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.IntSOfSIntFin
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.IntS

open Formalism.QuantumDeterminants

section frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

theorem gN_eq_frob {k r : ℕ} (g : Mat k r) : Formalism.FourierDecayAlt.B.gN g = ‖g‖ := by
  rw [frobenius_norm_def, Formalism.FourierDecayAlt.B.gN, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq, Real.rpow_two]

theorem gN_mul_le' {k r : ℕ} (A B : Mat k r) :
    Formalism.FourierDecayAlt.B.gN (A * B) ≤ Formalism.FourierDecayAlt.B.gN A * Formalism.FourierDecayAlt.B.gN B := by
  rw [gN_eq_frob, gN_eq_frob, gN_eq_frob]
  exact frobenius_norm_mul A B

theorem gN_pos_of_ne {k r : ℕ} {g : Mat k r} (hg : g ≠ 0) : 0 < Formalism.FourierDecayAlt.B.gN g := by
  rw [gN_eq_frob]; exact norm_pos_iff.mpr hg

end frob

theorem gN_nonneg' {k r : ℕ} (g : Mat k r) : 0 ≤ Formalism.FourierDecayAlt.B.gN g := Real.sqrt_nonneg _

theorem gN_continuous (k r : ℕ) : Continuous (fun g : Mat k r => Formalism.FourierDecayAlt.B.gN g) :=
  Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))

section hpk
variable (k r : ℕ)

theorem Hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  simp only [mulVec, dotProduct]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    simp only [Hpk_out k r h1]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp
  · rw [if_neg h1]
    simp only [Hpk_mid k r h1]
    rw [Finset.sum_eq_single i]
    · split_ifs <;> first | (exfalso; omega) | simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp

theorem Hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  ext i
  rw [Hpk_mulVec]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1, Hpk_mulVec]
    have e1 : ((⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)).val) = 2 * r + k - i.val := rfl
    rw [if_pos (by rw [e1]; omega)]
    congr 1; ext; simp; omega
  · rw [if_neg h1, Hpk_mulVec, if_neg h1]
    split_ifs <;> simp

theorem mat_eq_of_mulVec' {A B : Mat k r} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single j 1)) i

theorem Hpk_sq : Hpk k r * Hpk k r = 1 :=
  mat_eq_of_mulVec' k r fun v => by rw [← Matrix.mulVec_mulVec, Hpk_mulVec_mulVec, Matrix.one_mulVec]

variable {k r}

theorem UH_left_inv {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', Hpk_sq]

theorem UH_mul_inv {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 := by
  have h1 : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv (UH_left_inv hg)
  exact mul_eq_one_comm.mp (by rw [h1, UH_left_inv hg])

theorem UH_mul {g x : Mat k r} (hg : g ∈ UH (Hpk k r)) (hx : x ∈ UH (Hpk k r)) :
    g * x ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  show (g * x)ᴴ * Hpk k r * (g * x) = Hpk k r
  rw [conjTranspose_mul]
  calc xᴴ * gᴴ * Hpk k r * (g * x) = xᴴ * (gᴴ * Hpk k r * g) * x := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hx']

theorem ne_zero_of_mem_UH {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g ≠ 0 := by
  intro h
  have := UH_mul_inv hg
  rw [h, Matrix.zero_mul] at this
  exact zero_ne_one this

end hpk

theorem orbit_bound (k r : ℕ) (x₀ s x : Mat k r) (hx₀ : x₀ ∈ UH (Hpk k r)) (hs : s ∈ UH (Hpk k r))
    (hx : x ∈ UH (Hpk k r)) (b : ℝ) (hb : 0 ≤ b) :
    Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (s * x)) ^ (-b) ≤
      (Formalism.FourierDecayAlt.B.gN x₀ * Formalism.FourierDecayAlt.B.gN x⁻¹) ^ b * Formalism.FourierDecayAlt.B.gN s ^ (-b) := by
  set y := x₀⁻¹ * (s * x) with hy
  have hsy : x₀ * y * x⁻¹ = s := by
    rw [hy, ← Matrix.mul_assoc x₀, UH_mul_inv hx₀, Matrix.one_mul, Matrix.mul_assoc, UH_mul_inv hx,
      Matrix.mul_one]
  have hs0 : 0 < Formalism.FourierDecayAlt.B.gN s := gN_pos_of_ne (ne_zero_of_mem_UH hs)
  have hyne : y ≠ 0 := by
    intro h
    rw [h, Matrix.mul_zero, Matrix.zero_mul] at hsy
    exact ne_zero_of_mem_UH hs hsy.symm
  have hy0 : 0 < Formalism.FourierDecayAlt.B.gN y := gN_pos_of_ne hyne
  set A := Formalism.FourierDecayAlt.B.gN x₀ * Formalism.FourierDecayAlt.B.gN x⁻¹ with hA
  have hle : Formalism.FourierDecayAlt.B.gN s ≤ A * Formalism.FourierDecayAlt.B.gN y := by
    rw [← hsy]
    calc Formalism.FourierDecayAlt.B.gN (x₀ * y * x⁻¹) ≤ Formalism.FourierDecayAlt.B.gN (x₀ * y) * Formalism.FourierDecayAlt.B.gN x⁻¹ := gN_mul_le' _ _
      _ ≤ Formalism.FourierDecayAlt.B.gN x₀ * Formalism.FourierDecayAlt.B.gN y * Formalism.FourierDecayAlt.B.gN x⁻¹ :=
          mul_le_mul_of_nonneg_right (gN_mul_le' _ _) (gN_nonneg' _)
      _ = A * Formalism.FourierDecayAlt.B.gN y := by rw [hA]; ring
  have hA0 : 0 < A := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc hy0.le]
  have hpow : Formalism.FourierDecayAlt.B.gN s ^ b ≤ A ^ b * Formalism.FourierDecayAlt.B.gN y ^ b := by
    rw [← Real.mul_rpow hA0.le hy0.le]
    exact Real.rpow_le_rpow hs0.le hle hb
  have hSb : 0 < Formalism.FourierDecayAlt.B.gN s ^ b := Real.rpow_pos_of_pos hs0 b
  have hYb : 0 < Formalism.FourierDecayAlt.B.gN y ^ b := Real.rpow_pos_of_pos hy0 b
  rw [Real.rpow_neg hy0.le, Real.rpow_neg hs0.le, ← div_eq_mul_inv, le_div_iff₀ hSb,
    inv_mul_le_iff₀ hYb]
  linarith [mul_comm (A ^ b) (Formalism.FourierDecayAlt.B.gN y ^ b)]

theorem bS_nonneg (k r : ℕ) : 0 ≤ bS k r := by
  unfold bS nS; positivity

theorem bS_le_bS (k r : ℕ) : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bS k r ≤ bS k r :=
  le_of_le_of_eq (ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bS_le k r) (by unfold bS nS ReciprocityTheory.ChartRestriction.DS.Mult1.nR; rfl)

theorem intS_of_sIntFin (h : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.SIntFin) : IntSStatement := by
  intro k r z μW μN hz hT hW hN x₀ hx₀ x hx b hb
  have hb0 : 0 ≤ b := le_trans (bS_nonneg k r) hb.le
  have hb1 : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bS k r < b := lt_of_le_of_lt (bS_le_bS k r) hb
  have hfin := (h k r z μW μN hz hT hW hN b hb1).1
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have hcont : Continuous (fun p : Mt k r × Mt k r =>
      Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x))) :=
    (gN_continuous k r).comp (continuous_const.matrix_mul
      ((continuous_fst.matrix_mul continuous_snd).matrix_mul continuous_const))
  have hmeas : Measurable (fun p : Mt k r × Mt k r =>
      Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) ^ (-b)) :=
    hcont.measurable.pow_const _
  have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := by
    rw [ae_iff]
    have e : {p : Mt k r × Mt k r | ¬ Matrix.of p.1 ∈ UWset k r z} =
        {y : Mt k r | Matrix.of y ∉ UWset k r z} ×ˢ (Set.univ : Set (Mt k r)) := by
      ext p; simp
    rw [e, Measure.prod_prod, hW.2.2.1, zero_mul]
  have h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := by
    rw [ae_iff]
    have e : {p : Mt k r × Mt k r | ¬ Matrix.of p.2 ∈ Nset k r} =
        (Set.univ : Set (Mt k r)) ×ˢ {y : Mt k r | Matrix.of y ∉ Nset k r} := by
      ext p; simp
    rw [e, Measure.prod_prod, hN.2.2.1, mul_zero]
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => Real.rpow_nonneg (gN_nonneg' _) _)]
  calc ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) ^ (-b)) ∂(μW.prod μN)
      ≤ ∫⁻ p, ENNReal.ofReal ((Formalism.FourierDecayAlt.B.gN x₀ * Formalism.FourierDecayAlt.B.gN x⁻¹) ^ b) *
          ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b)) ∂(μW.prod μN) := by
        refine lintegral_mono_ae ((h1.and h2).mono fun p hp => ?_)
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg (gN_nonneg' _) (gN_nonneg' _)) _)]
        exact ENNReal.ofReal_le_ofReal
          (orbit_bound k r x₀ _ x hx₀ (UH_mul hp.1.1 hp.2.1) hx b hb0)
    _ = ENNReal.ofReal ((Formalism.FourierDecayAlt.B.gN x₀ * Formalism.FourierDecayAlt.B.gN x⁻¹) ^ b) *
          ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b)) ∂(μW.prod μN) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.IntS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.OneLeGN
section
noncomputable section

open Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.DecA

open Formalism.QuantumDeterminants

def sg (k r i : ℕ) : ℕ := if i < r ∨ r + k < i then 2 * r + k - i else i

theorem hpk_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = sg k r i.val then (if i.val = r + k then -1 else 1) else 0 := by
  unfold Hpk sg
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    rcases h1 with h1 | h1
    · by_cases h2 : i.val + j.val = 2 * r + k
      · rw [if_pos ⟨h1, h2⟩, if_pos (by omega), if_neg (by omega)]
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2), if_neg (by omega), if_neg (by omega)]
    · by_cases h2 : i.val + j.val = 2 * r + k
      · rw [if_neg (by omega), if_pos ⟨by omega, h2⟩, if_pos (by omega), if_neg (by omega)]
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2), if_neg (by omega), if_neg (by omega)]
  · rw [if_neg h1]
    push Not at h1
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases h2 : i = j
    · subst h2; rw [if_pos ⟨h1.1, h1.2, rfl⟩, if_pos rfl]
    · rw [if_neg (fun h => h2 h.2.2), if_neg (fun h => h2 (Fin.ext h.symm))]

theorem hpk_symm (k r : ℕ) (i j : Fin (2 * r + k + 1)) : Hpk k r j i = Hpk k r i j := by
  rw [hpk_apply, hpk_apply]; unfold sg
  split_ifs <;> first | rfl | omega

theorem hpk_conjT (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, hpk_symm, hpk_apply]
  split_ifs <;> simp

theorem sg_lt {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r i < 2 * r + k + 1 := by
  unfold sg; split_ifs <;> omega

theorem sg_sg {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r (sg k r i) = i := by
  unfold sg; split_ifs <;> omega

theorem sg_rk {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r i = r + k ↔ i = r + k := by
  unfold sg; split_ifs <;> omega

theorem hpk_apply' (k r i : ℕ) (hi : i < 2 * r + k + 1) (j : Fin (2 * r + k + 1)) :
    Hpk k r ⟨i, hi⟩ j = if j.val = sg k r i then (if i = r + k then -1 else 1) else 0 :=
  hpk_apply k r ⟨i, hi⟩ j

theorem hpk_mul (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨sg k r i.val, sg_lt i.2⟩ : Fin _)]
  · rw [hpk_apply k r i ⟨sg k r i.val, sg_lt i.2⟩, hpk_apply' k r _ (sg_lt i.2) j, sg_sg i.2, Matrix.one_apply,
      if_pos (show ((⟨sg k r i.val, sg_lt i.2⟩ : Fin (2 * r + k + 1)).val = sg k r i.val) from rfl)]
    have hs := sg_rk (k := k) (r := r) i.2
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl]
      by_cases h : i.val = r + k
      · rw [if_pos h, if_pos (hs.2 h)]; norm_num
      · rw [if_neg h, if_neg (fun h' => h (hs.1 h'))]; norm_num
    · rw [if_neg hij, if_neg (fun h : j.val = i.val => hij (Fin.ext h.symm)), mul_zero]
  · intro b _ hb; rw [hpk_apply k r i b, if_neg (fun h => hb (Fin.ext h)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem inv_eq {k r : ℕ} {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  refine Matrix.inv_eq_left_inv ?_
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_mul]

theorem inv_mul {k r : ℕ} {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [inv_eq hg]
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_mul]

theorem mul_inv {k r : ℕ} {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 :=
  mul_eq_one_comm.mp (inv_mul hg)

theorem inv_mem {k r : ℕ} {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have h1 : g * g⁻¹ = 1 := mul_inv hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1]; simp

theorem gN_nonneg {k r : ℕ} (g : Mat k r) : 0 ≤ Formalism.FourierDecayAlt.B.gN g := Real.sqrt_nonneg _

theorem gN_sq {k r : ℕ} (g : Mat k r) : (∑ i, ∑ j, Complex.normSq (g i j)) = (trace (gᴴ * g)).re := by
  simp only [trace, diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

theorem gN_left {k r : ℕ} {κ : Mat k r} (g : Mat k r) (hκ : κᴴ * κ = 1) :
    Formalism.FourierDecayAlt.B.gN (κ * g) = Formalism.FourierDecayAlt.B.gN g := by
  unfold Formalism.FourierDecayAlt.B.gN
  rw [gN_sq, gN_sq, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]

theorem gN_right {k r : ℕ} {κ : Mat k r} (g : Mat k r) (hκ : κᴴ * κ = 1) :
    Formalism.FourierDecayAlt.B.gN (g * κ) = Formalism.FourierDecayAlt.B.gN g := by
  have hκ' : κ * κᴴ = 1 := mul_eq_one_comm.mp hκ
  unfold Formalism.FourierDecayAlt.B.gN
  rw [gN_sq, gN_sq, conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, hκ', Matrix.mul_one]

theorem gN_conjT {k r : ℕ} (g : Mat k r) : Formalism.FourierDecayAlt.B.gN gᴴ = Formalism.FourierDecayAlt.B.gN g := by
  unfold Formalism.FourierDecayAlt.B.gN
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [conjTranspose_apply, Complex.star_def, Complex.normSq_conj]

theorem gN_entry {k r : ℕ} (g : Mat k r) (i j : Fin (2 * r + k + 1)) : ‖g i j‖ ≤ Formalism.FourierDecayAlt.B.gN g := by
  unfold Formalism.FourierDecayAlt.B.gN
  rw [← Real.sqrt_sq (norm_nonneg (g i j)), ← Complex.normSq_eq_norm_sq]
  refine Real.sqrt_le_sqrt ?_
  calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (g i j')) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

section frob

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

theorem gN_eq_norm {k r : ℕ} (g : Mat k r) : Formalism.FourierDecayAlt.B.gN g = ‖g‖ := by
  rw [Matrix.frobenius_norm_def, Formalism.FourierDecayAlt.B.gN, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq, Real.rpow_two]

theorem gN_mul_le' {k r : ℕ} (a b : Mat k r) :
    Formalism.FourierDecayAlt.B.gN (a * b) ≤ Formalism.FourierDecayAlt.B.gN a * Formalism.FourierDecayAlt.B.gN b := by
  rw [gN_eq_norm, gN_eq_norm, gN_eq_norm]
  exact Matrix.frobenius_norm_mul a b

end frob

theorem gN_inv' {k r : ℕ} {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : Formalism.FourierDecayAlt.B.gN g⁻¹ = Formalism.FourierDecayAlt.B.gN g := by
  have hH : (Hpk k r)ᴴ * Hpk k r = 1 := by rw [hpk_conjT, hpk_mul]
  rw [inv_eq hg, gN_right _ hH, gN_left _ hH, gN_conjT]

theorem one_le_gN' {k r : ℕ} {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : 1 ≤ Formalism.FourierDecayAlt.B.gN g := by
  have h0 : (1 : ℝ) ≤ Formalism.FourierDecayAlt.B.gN (1 : Mat k r) := by
    have := gN_entry (1 : Mat k r) ⟨0, by omega⟩ ⟨0, by omega⟩
    simpa using this
  have h1 : Formalism.FourierDecayAlt.B.gN (1 : Mat k r) ≤ Formalism.FourierDecayAlt.B.gN g * Formalism.FourierDecayAlt.B.gN g := by
    have := gN_mul_le' g g⁻¹
    rwa [mul_inv hg, gN_inv' hg] at this
  nlinarith [gN_nonneg g]

theorem pb_real (a A B Y : ℝ) (ha : 0 ≤ a) (hA : 1 ≤ A) (hB : 1 ≤ B) (hY : 0 < Y) (hYB : Y ≤ B * A)
    (hAB : A ≤ B) : A ^ (-a) * B ^ (-a) ≤ Y ^ (-(a / 4)) * B ^ (-(a / 2)) := by
  have hB0 : 0 ≤ B := by linarith
  have hA1 : A ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA (by linarith)
  have hBpos : 0 ≤ B ^ (-a) := Real.rpow_nonneg hB0 _
  have hYBB : Y ≤ B ^ (2 : ℝ) := by
    rw [Real.rpow_two]; nlinarith
  have h2 : B ^ (-(a / 2)) ≤ Y ^ (-(a / 4)) := by
    have := Real.rpow_le_rpow_of_nonpos hY hYBB (show -(a / 4) ≤ 0 by linarith)
    rwa [← Real.rpow_mul hB0, show (2 : ℝ) * -(a / 4) = -(a / 2) by ring] at this
  have h3 : B ^ (-a) = B ^ (-(a / 2)) * B ^ (-(a / 2)) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have hBh : 0 ≤ B ^ (-(a / 2)) := Real.rpow_nonneg hB0 _
  calc A ^ (-a) * B ^ (-a) ≤ 1 * B ^ (-a) := mul_le_mul_of_nonneg_right hA1 hBpos
    _ = B ^ (-(a / 2)) * B ^ (-(a / 2)) := by rw [one_mul, h3]
    _ ≤ Y ^ (-(a / 4)) * B ^ (-(a / 2)) := mul_le_mul_of_nonneg_right h2 hBh

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.DecA
end
end

