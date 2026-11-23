module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0006

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.FockTA
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

section Gen

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem fockT_cm_cp {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) {ε : Fin n → Bool}
    {j b u v : Fin n} (hjb : ¬(ε j = true ∧ ε b = false)) (huv : ε u = true ∧ ε v = false) (y : W) :
    cm j b (cp u v y) = -(cp u v (cm j b y)) := by
  have h3 := (hC j b u v).2.2
  have hne : ¬(j = u ∧ b = v) := by
    rintro ⟨rfl, rfl⟩
    exact hjb huv
  rw [if_neg hne] at h3
  have h := LinearMap.congr_fun h3 y
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  exact eq_neg_of_add_eq_zero_left h

theorem fockT_cm_cm {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (j b w z : Fin n) (y : W) :
    cm j b (cm w z y) = -(cm w z (cm j b y)) := by
  have h := LinearMap.congr_fun (hC j b w z).2.1 y
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  exact eq_neg_of_add_eq_zero_left h

theorem fockT_stable_gen {E cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (hK : CommutesCAR E cp cm) (ε : Fin n → Bool) {j b : Fin n} (hjb : ¬(ε j = true ∧ ε b = false))
    {x : W} (hx : ∀ j b, ¬(ε j = true ∧ ε b = false) → cm j b x = 0) :
    (∀ a c, cm j b (E a c x) = 0) ∧ (∀ a c, cm j b (diagE ε E cp cm a c x) = 0) ∧
      cm j b (dOp ε E cp x) = 0 ∧ cm j b (dOp' ε E cm x) = 0 := by
  have hEc : ∀ a c y, cm j b (E a c y) = E a c (cm j b y) := fun a c y => by
    have h := LinearMap.congr_fun (hK a c j b).2 y
    simp only [Module.End.mul_apply] at h
    exact h.symm
  have hx0 := hx j b hjb
  have hE0 : ∀ a c, cm j b (E a c x) = 0 := fun a c => by rw [hEc, hx0, map_zero]
  have hcpcm : ∀ u v w z, ε u = true ∧ ε v = false → cm j b (cp u v (cm w z x)) = 0 := by
    intro u v w z huv
    rw [fockT_cm_cp hC hjb huv, fockT_cm_cm hC, hx0]
    simp
  refine ⟨hE0, ?_, ?_, ?_⟩
  · intro a c
    simp only [diagE, LinearMap.add_apply, map_add (f := _), hE0, zero_add, sgE]
    by_cases ha : ε a = true <;> by_cases hc : ε c = true
    · simp only [if_pos (And.intro ha hc), LinearMap.sum_apply, map_sum, Module.End.mul_apply]
      refine Finset.sum_eq_zero fun y hy => hcpcm a y c y ⟨ha, ?_⟩
      simpa [minusIdx] using hy
    · simp [ha, hc, sgE]
    · simp [ha, hc, sgE]
    · have ha0 : ε a = false := by cases h : ε a <;> simp_all
      have hc0 : ε c = false := by cases h : ε c <;> simp_all
      simp only [if_neg (show ¬(ε a = true ∧ ε c = true) from fun h => ha h.1),
        if_pos (And.intro ha0 hc0), LinearMap.neg_apply, LinearMap.sum_apply, map_neg, map_sum,
        Module.End.mul_apply]
      refine neg_eq_zero.mpr (Finset.sum_eq_zero fun i hi => hcpcm i c i a ⟨?_, hc0⟩)
      simpa [plusIdx] using hi
  · simp only [dOp, LinearMap.sum_apply, map_sum, Module.End.mul_apply]
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun a ha => ?_
    rw [hEc, fockT_cm_cp hC hjb ⟨by simpa [plusIdx] using hi, by simpa [minusIdx] using ha⟩, hx0]
    simp
  · simp only [dOp', LinearMap.neg_apply, LinearMap.sum_apply, map_neg, map_sum, Module.End.mul_apply]
    refine neg_eq_zero.mpr (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun a _ => ?_)
    rw [hEc, fockT_cm_cm hC, hx0]
    simp

theorem fockT_anti_sum {R : Type*} [Ring R] {ι κ : Type*} (s : Finset ι) (t : Finset κ) (G : R)
    (A B : ι → κ → R) (hA : ∀ i k, G * A i k = A i k * G) (hB : ∀ i k, G * B i k = -(B i k * G)) :
    G * ∑ i ∈ s, ∑ k ∈ t, A i k * B i k = -((∑ i ∈ s, ∑ k ∈ t, A i k * B i k) * G) := by
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  calc G * (A i k * B i k) = A i k * (G * B i k) := by rw [← mul_assoc, hA, mul_assoc]
    _ = -(A i k * B i k * G) := by rw [hB, mul_neg, mul_assoc]

end Gen

section FockLemmas

variable {n : ℕ}

theorem fock_contractLeft_involute (d : Module.Dual ℂ (Fin n × Fin n → ℂ)) (x : Fock n) :
    CliffordAlgebra.contractLeft d (CliffordAlgebra.involute x) =
      -CliffordAlgebra.involute (CliffordAlgebra.contractLeft d x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, neg_add]
  | ι_mul x m hx =>
    simp only [map_mul, CliffordAlgebra.involute_ι, neg_mul, map_neg, CliffordAlgebra.contractLeft_ι_mul,
      hx, map_sub, map_smul, mul_neg]

theorem fock_inv_sq :
    (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap *
      (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap = 1 :=
  LinearMap.ext fun x => CliffordAlgebra.involute_involute x

theorem fock_inv_cp (i a : Fin n) :
    (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap * cpFock i a =
      -(cpFock i a * (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap) := by
  refine LinearMap.ext fun x => ?_
  simp [cpFock, CliffordAlgebra.involute_ι]

theorem fock_inv_cm (i a : Fin n) :
    (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap * cmFock i a =
      -(cmFock i a * (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap) := by
  refine LinearMap.ext fun x => ?_
  simp [cmFock, fock_contractLeft_involute]

end FockLemmas

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockC
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def lowerWedgeAlt (ε : Fin n → Bool) : LfIdx ε :=
  ⟨(lfPhysModes ε).filter fun m => (finProdFinEquiv.symm m).2 < (finProdFinEquiv.symm m).1, filter_subset _ _⟩

theorem mem_lowerWedge_iff (ε : Fin n → Bool) (x : Fin n × Fin n) :
    finProdFinEquiv x ∈ (lowerWedgeAlt ε).1 ↔ ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 := by
  simp only [lowerWedgeAlt, lfPhysModes, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply,
    and_assoc]

theorem lf_rhoHol_sub_rhoN (ε : Fin n → Bool) (c : Fin n) :
    (rhoHol ε - rhoN ε) c = if ε c = true then ((univ.filter fun a => ε a = false ∧ a < c).card : ℝ)
      else -((univ.filter fun i => ε i = true ∧ c < i).card : ℝ) := by
  rw [cfa_rho_coord]
  cases hc : ε c <;> simp [hc, Finset.sum_boole]

theorem lowerWedge_weight (ε : Fin n → Bool) (c : Fin n) :
    sgE ε cpFock cmFock c c (fockBasis n (lowerWedgeAlt ε).1) =
      (((rhoHol ε - rhoN ε) c : ℝ) : ℂ) • fockBasis n (lowerWedgeAlt ε).1 := by
  have hw : fockWt ε (lowerWedgeAlt ε).1 c = (rhoHol ε - rhoN ε) c := by
    rw [cfa_rho_coord, fockWt, Finset.sum_apply]
    have hS : (lowerWedgeAlt ε).1 = univ.filter fun k => ε (finProdFinEquiv.symm k).1 = true ∧
        ε (finProdFinEquiv.symm k).2 = false ∧ (finProdFinEquiv.symm k).2 < (finProdFinEquiv.symm k).1 := by
      ext k
      simp only [lowerWedgeAlt, lfPhysModes, Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
    rw [hS, Finset.sum_filter, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply]
    have key : ∀ i b : Fin n, (if ε i = true ∧ ε b = false ∧ b < i then modeWt ε (i, b) c else 0) =
        (if c = i then (if ε i = true ∧ ε b = false ∧ b < i then (1 : ℝ) else 0) else 0) -
        (if c = b then (if ε i = true ∧ ε b = false ∧ b < i then (1 : ℝ) else 0) else 0) := by
      intro i b
      by_cases h : ε i = true ∧ ε b = false ∧ b < i
      · simp only [if_pos h]
        simp only [modeWt, if_pos (And.intro h.1 h.2.1), root, Pi.sub_apply, Pi.single_apply]
      · simp only [if_neg h]
        simp
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => key i b]
    simp only [Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_comm]
      simp
    · simp
  rw [fockBasis_wt, hw]

theorem lowerWedge_killed_by_lowering (ε : Fin n → Bool) {a b : Fin n} (hba : b < a) (he : ε a = ε b) :
    sgE ε cpFock cmFock a b (fockBasis n (lowerWedgeAlt ε).1) = 0 := by
  have hab : a ≠ b := (ne_of_lt hba).symm
  unfold sgE
  split_ifs with h1 h2
  · rw [LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hxm : ε x = false := (Finset.mem_filter.1 hx).2
    rw [Module.End.mul_apply]
    by_cases hbx : finProdFinEquiv (b, x) ∈ (lowerWedgeAlt ε).1
    · obtain ⟨σ, -, hσ, -⟩ := lf_cm_basis_of_mem (x := (b, x)) hbx
      dsimp only at hσ
      rw [hσ, map_smul]
      have hxb : x < b := ((mem_lowerWedge_iff ε (b, x)).1 hbx).2.2
      have hmem : finProdFinEquiv (a, x) ∈ (lowerWedgeAlt ε).1.erase (finProdFinEquiv (b, x)) := by
        rw [Finset.mem_erase]
        exact ⟨fun h => hab (congrArg Prod.fst (finProdFinEquiv.injective h)),
          (mem_lowerWedge_iff ε (a, x)).2 ⟨h1.1, hxm, hxb.trans hba⟩⟩
      have h0 := lf_cp_basis_of_mem (x := (a, x)) hmem
      dsimp only at h0
      rw [h0, smul_zero]
    · have h0 := lf_cm_basis_of_not_mem (x := (b, x)) hbx
      dsimp only at h0
      rw [h0, map_zero]
  · rw [LinearMap.neg_apply, LinearMap.sum_apply, neg_eq_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hip : ε i = true := (Finset.mem_filter.1 hi).2
    rw [Module.End.mul_apply]
    by_cases hia : finProdFinEquiv (i, a) ∈ (lowerWedgeAlt ε).1
    · obtain ⟨σ, -, hσ, -⟩ := lf_cm_basis_of_mem (x := (i, a)) hia
      dsimp only at hσ
      rw [hσ, map_smul]
      have hai : a < i := ((mem_lowerWedge_iff ε (i, a)).1 hia).2.2
      have hmem : finProdFinEquiv (i, b) ∈ (lowerWedgeAlt ε).1.erase (finProdFinEquiv (i, a)) := by
        rw [Finset.mem_erase]
        exact ⟨fun h => hab (congrArg Prod.snd (finProdFinEquiv.injective h)).symm,
          (mem_lowerWedge_iff ε (i, b)).2 ⟨hip, h2.2, hba.trans hai⟩⟩
      have h0 := lf_cp_basis_of_mem (x := (i, b)) hmem
      dsimp only at h0
      rw [h0, smul_zero]
    · have h0 := lf_cm_basis_of_not_mem (x := (i, a)) hia
      dsimp only at h0
      rw [h0, map_zero]
  · exfalso
    cases hb : ε b <;> simp_all

end ReciprocityTheory.ChartRestriction.DS
end
end

