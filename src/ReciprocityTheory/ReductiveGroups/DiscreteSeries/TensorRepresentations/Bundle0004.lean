module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PartialTrace

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARSqB
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem isCAR_cm_mul_cp_eq_delta_sub_cp_mul_cm {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (i a j b : Fin n) :
    cm i a * cp j b = (if i = j ∧ a = b then 1 else 0) - cp j b * cm i a :=
  eq_sub_of_add_eq (hC i a j b).2.2

private theorem isCAR_cm_mul_cm_eq_neg_swap {cp cm : Fin n → Fin n → Module.End ℂ W}
    (hC : IsCAR cp cm) (i a j b : Fin n) :
    cm i a * cm j b = -(cm j b * cm i a) :=
  eq_neg_of_add_eq_zero_left (hC i a j b).2.1

private theorem sum_sum_ite_eq_eq_sum {R ι : Type*} [AddCommMonoid R] [DecidableEq ι] (s : Finset ι)
    (f : ι → R) : ∑ x ∈ s, ∑ y ∈ s, (if x = y then f x else 0) = ∑ x ∈ s, f x :=
  Finset.sum_congr rfl fun x hx => by simp [hx]

private theorem isCAR_cp_cm_cp_cm_reorder_shared_snd {cp cm : Fin n → Fin n → Module.End ℂ W}
    (hC : IsCAR cp cm) (a b x y : Fin n) :
    cp a x * cm b x * (cp b y * cm a y) =
      (if x = y then cp a x * cm a x else 0) - cp a x * cp b y * (cm b x * cm a y) := by
  rw [show cp a x * cm b x * (cp b y * cm a y) = cp a x * (cm b x * cp b y) * cm a y by
    simp only [mul_assoc], isCAR_cm_mul_cp_eq_delta_sub_cp_mul_cm hC b x b y]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
    noncomm_ring
  · rw [if_neg (fun h => hxy h.2), if_neg hxy]
    noncomm_ring

private theorem isCAR_cp_cm_cp_cm_reorder_shared_fst {cp cm : Fin n → Fin n → Module.End ℂ W}
    (hC : IsCAR cp cm) (a b i j : Fin n) :
    cp i b * cm i a * (cp j a * cm j b) =
      (if i = j then cp i b * cm i b else 0) - cp i b * cp j a * (cm i a * cm j b) := by
  rw [show cp i b * cm i a * (cp j a * cm j b) = cp i b * (cm i a * cp j a) * cm j b by
    simp only [mul_assoc], isCAR_cm_mul_cp_eq_delta_sub_cp_mul_cm hC i a j a]
  by_cases hij : i = j
  · subst hij
    rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
    noncomm_ring
  · rw [if_neg (fun h => hij h.1), if_neg hij]
    noncomm_ring

theorem casimirK_sgE {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (ε : Fin n → Bool) :
    casimirK ε (sgE ε cp cm) = (2 : ℂ) • ∑ a, ((rhoHol ε a : ℝ) : ℂ) • sgE ε cp cm a a := by
  have hpos : ∀ a ∈ plusIdx ε, ∀ b ∈ plusIdx ε,
      sgE ε cp cm a b * sgE ε cp cm b a =
        ∑ x ∈ minusIdx ε, ∑ y ∈ minusIdx ε,
          ((if x = y then cp a x * cm a x else 0) - cp a x * cp b y * (cm b x * cm a y)) := by
    intro a ha b hb
    rw [csq_sgE_pp ε cp cm ha hb, csq_sgE_pp ε cp cm hb ha, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => isCAR_cp_cm_cp_cm_reorder_shared_snd hC a b x y
  have hneg : ∀ a ∈ minusIdx ε, ∀ b ∈ minusIdx ε,
      sgE ε cp cm a b * sgE ε cp cm b a =
        ∑ i ∈ plusIdx ε, ∑ j ∈ plusIdx ε,
          ((if i = j then cp i b * cm i b else 0) - cp i b * cp j a * (cm i a * cm j b)) := by
    intro a ha b hb
    rw [csq_sgE_mm ε cp cm ha hb, csq_sgE_mm ε cp cm hb ha, neg_mul_neg,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => isCAR_cp_cm_cp_cm_reorder_shared_fst hC a b i j
  have hposBlock : ∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε,
      sgE ε cp cm a b * sgE ε cp cm b a =
        (pOf ε : ℂ) •
            ∑ a ∈ plusIdx ε, ∑ x ∈ minusIdx ε, cp a x * cm a x -
          ∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε, ∑ x ∈ minusIdx ε,
            ∑ y ∈ minusIdx ε, cp a x * cp b y * (cm b x * cm a y) := by
    rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hpos a ha b hb]
    simp only [Finset.sum_sub_distrib, sum_sum_ite_eq_eq_sum, Finset.sum_const, ← Finset.smul_sum]
    rw [Nat.cast_smul_eq_nsmul ℂ]
    rfl
  have hnegBlock : ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε,
      sgE ε cp cm a b * sgE ε cp cm b a =
        (qOf ε : ℂ) •
            ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, cp i b * cm i b -
          ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε,
            ∑ j ∈ plusIdx ε, cp i b * cp j a * (cm i a * cm j b) := by
    rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hneg a ha b hb]
    simp only [Finset.sum_sub_distrib, sum_sum_ite_eq_eq_sum, Finset.sum_const]
    rw [Nat.cast_smul_eq_nsmul ℂ]
    rfl
  have hT : ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε,
        ∑ j ∈ plusIdx ε, cp i b * cp j a * (cm i a * cm j b) =
      -∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε, ∑ x ∈ minusIdx ε,
        ∑ y ∈ minusIdx ε, cp a x * cp b y * (cm b x * cm a y) := by
    rw [sum_comm_pair_pair, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [isCAR_cm_mul_cm_eq_neg_swap hC i a j b, mul_neg]
  have hN : ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, cp i b * cm i b =
      ∑ a ∈ plusIdx ε, ∑ x ∈ minusIdx ε, cp a x * cm a x := by
    rw [Finset.sum_comm]
  have hR1 : ∑ a ∈ plusIdx ε, (qOf ε : ℂ) • sgE ε cp cm a a =
      (qOf ε : ℂ) •
        ∑ a ∈ plusIdx ε, ∑ x ∈ minusIdx ε, cp a x * cm a x := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun a ha => by rw [csq_sgE_pp ε cp cm ha ha]
  have hR2 : ∑ a ∈ minusIdx ε, (pOf ε : ℂ) • sgE ε cp cm a a =
      -((pOf ε : ℂ) •
        ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, cp i b * cm i b) := by
    rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a ha => by rw [csq_sgE_mm ε cp cm ha ha, smul_neg]
  rw [casimirK_pm, two_rho_sum, hposBlock,
    hnegBlock, hR1, hR2, hT, hN]
  abel

theorem csq_E_comm_sgE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hEC : CommutesCAR E cp cm)
    (ε : Fin n → Bool) (x y a b : Fin n) :
    E x y * sgE ε cp cm a b = sgE ε cp cm a b * E x y := by
  unfold sgE
  split_ifs
  · rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← mul_assoc, (hEC x y a z).1, mul_assoc, (hEC x y b z).2, ← mul_assoc]
  · rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, (hEC x y i b).1, mul_assoc, (hEC x y i a).2, ← mul_assoc]
  · rw [mul_zero, zero_mul]

def crossT (ε : Fin n → Bool) (E cp cm : Fin n → Fin n → Module.End ℂ W) : Module.End ℂ W :=
  ∑ x ∈ plusIdx ε, ∑ y ∈ plusIdx ε, E x y * sgE ε cp cm y x +
    ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, E a b * sgE ε cp cm b a

private theorem sum_sum_add_mul_add_of_commute (s : Finset (Fin n)) (E S : Fin n → Fin n → Module.End ℂ W)
    (h : ∀ a b c d, S a b * E c d = E c d * S a b) :
    ∑ a ∈ s, ∑ b ∈ s, (E a b + S a b) * (E b a + S b a) =
      ∑ a ∈ s, ∑ b ∈ s, E a b * E b a + (2 : ℂ) • ∑ a ∈ s, ∑ b ∈ s, E a b * S b a +
        ∑ a ∈ s, ∑ b ∈ s, S a b * S b a := by
  have hsw : ∑ a ∈ s, ∑ b ∈ s, S a b * E b a = ∑ a ∈ s, ∑ b ∈ s, E a b * S b a := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => h b a a b
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  rw [hsw, two_smul]
  abel

theorem casimirK_diagE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hEC : CommutesCAR E cp cm)
    (ε : Fin n → Bool) :
    casimirK ε (diagE ε E cp cm) =
      casimirK ε E + (2 : ℂ) • crossT ε E cp cm + casimirK ε (sgE ε cp cm) := by
  have hc : ∀ a b c d, sgE ε cp cm a b * E c d = E c d * sgE ε cp cm a b :=
    fun a b c d => (csq_E_comm_sgE hEC ε c d a b).symm
  simp only [casimirK_pm, diagE, crossT]
  rw [sum_sum_add_mul_add_of_commute (plusIdx ε) E (sgE ε cp cm) hc,
    sum_sum_add_mul_add_of_commute (minusIdx ε) E (sgE ε cp cm) hc, smul_add]
  abel

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Resolvent
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def HasGelfandChar (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (S : Submodule ℂ M) : Prop :=
  ∀ k : ℕ, ∀ x ∈ S, gelfand E k x = gval (icShift μ) k • x ∧
    gelfand (antiE E) k x = gval (icShift (-μ)) k • x

def resSeries (a : Fin n → ℂ) : PowerSeries ℂ :=
  ∏ s, (1 + PowerSeries.X * (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹) - 1

def poleV (μ : Fin n → ℝ) : Fin n → ℂ := fun s => ((μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ)

def poleVd (μ : Fin n → ℝ) : Fin n → ℂ := fun s => ((-μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ)

theorem rescale_neg_one_const (c : ℂ) :
    PowerSeries.rescale (-1 : ℂ) (PowerSeries.C c) = PowerSeries.C c := by
  ext m
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h
  · simp [h]
  · simp

theorem rescale_neg_one_geometric_inv (c : ℂ) :
    PowerSeries.rescale (-1 : ℂ) ((1 - PowerSeries.C c * PowerSeries.X)⁻¹) =
      (1 + PowerSeries.C c * PowerSeries.X)⁻¹ := by
  have h1 : PowerSeries.rescale (-1 : ℂ) (1 - PowerSeries.C c * PowerSeries.X) =
      1 + PowerSeries.C c * PowerSeries.X := by
    simp [PowerSeries.rescale_X, rescale_neg_one_const]
  have hc0 : PowerSeries.constantCoeff (1 - PowerSeries.C c * PowerSeries.X) ≠ 0 := by simp
  have hc1 : PowerSeries.constantCoeff (1 + PowerSeries.C c * PowerSeries.X) ≠ 0 := by simp
  rw [PowerSeries.eq_inv_iff_mul_eq_one hc1, ← h1, ← map_mul, PowerSeries.inv_mul_cancel _ hc0, map_one]

theorem residueSeries_neg (l : Fin n → ℂ) :
    resSeries (-l) = -PowerSeries.rescale (-1 : ℂ) (gelfandSeries l) := by
  have key : ∀ s, (1 + PowerSeries.X * (1 - PowerSeries.C ((-l) s) * PowerSeries.X)⁻¹) =
      PowerSeries.rescale (-1 : ℂ) (1 - PowerSeries.X * (1 - PowerSeries.C (l s) * PowerSeries.X)⁻¹) := by
    intro s
    rw [map_sub, map_one, map_mul, PowerSeries.rescale_X, rescale_neg_one_geometric_inv]
    simp only [Pi.neg_apply, map_neg, map_one, neg_mul, one_mul, sub_neg_eq_add]
  unfold resSeries gelfandSeries
  simp_rw [key]
  rw [← map_prod, map_sub, map_one]
  ring

theorem coeff_residueSeries_neg (l : Fin n → ℂ) (k : ℕ) :
    PowerSeries.coeff (k + 1) (resSeries (-l)) = (-1 : ℂ) ^ k * gval l k := by
  rw [residueSeries_neg, map_neg, PowerSeries.coeff_rescale]
  unfold gval
  ring

theorem pole_eq_neg_shift (μ : Fin n → ℝ) : poleV μ = -icShift (-μ) := by
  funext s
  simp only [poleV, icShift, Pi.neg_apply]
  push_cast
  ring

theorem dualPole_eq_neg_shift (μ : Fin n → ℝ) : poleVd μ = -icShift μ := by
  funext s
  simp only [poleVd, icShift, Pi.neg_apply]
  push_cast
  ring

theorem ptr_eeV_pow_char {E : Fin n → Fin n → Module.End ℂ M} {μ : Fin n → ℝ} {S : Submodule ℂ M}
    (hS : HasGelfandChar E μ S) (k : ℕ) (x : M) (hx : x ∈ S) :
    ptr (eeV E ^ k) x = PowerSeries.coeff (k + 1) (resSeries (poleV μ)) • x := by
  rw [ptr_eeV_pow, LinearMap.smul_apply, (hS k x hx).2, smul_smul, pole_eq_neg_shift, coeff_residueSeries_neg]

theorem ptr_eeVd_pow_char {E : Fin n → Fin n → Module.End ℂ M} {μ : Fin n → ℝ} {S : Submodule ℂ M}
    (hS : HasGelfandChar E μ S) (k : ℕ) (x : M) (hx : x ∈ S) :
    ptr (eeVd E ^ k) x = PowerSeries.coeff (k + 1) (resSeries (poleVd μ)) • x := by
  rw [ptr_eeVd_pow, LinearMap.smul_apply, (hS k x hx).1, smul_smul, dualPole_eq_neg_shift, coeff_residueSeries_neg]

end ReciprocityTheory.ChartRestriction.DS
end
end

