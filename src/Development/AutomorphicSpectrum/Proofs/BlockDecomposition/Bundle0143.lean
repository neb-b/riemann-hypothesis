module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0130
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCoboundaryFormula
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.Prism

theorem prism_sum {R G : Type} [CommRing R] [AddCommGroup G] [Module R G] (N : ℕ) (a b : ℕ → ℕ → G)
    (h1 : ∀ k j, k < N → j ≤ k → a (k + 1) j = b k j)
    (h2 : ∀ k j, k < N → k < j → j < N + 1 → a k (j + 1) = b k j)
    (h3 : ∀ k, k < N → a k (k + 1) = a (k + 1) (k + 1)) :
    ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 2), ((-1 : R) ^ (i + j)) • a i j =
      a 0 0 - a N (N + 1) - ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (N + 1), ((-1 : R) ^ (k + j)) • b k j := by
  have row : ∀ i, i ≤ N → ∑ j ∈ Finset.range (N + 2), ((-1 : R) ^ (i + j)) • a i j =
      ∑ j ∈ Finset.range i, ((-1 : R) ^ (i + j)) • a i j + (a i i - a i (i + 1)) +
        ∑ j ∈ Finset.Ico (i + 1) (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) := by
    intro i hi
    have e1 := Finset.sum_range_add_sum_Ico (fun j ↦ ((-1 : R) ^ (i + j)) • a i j) (show i ≤ N + 2 by omega)
    have e2 : ∑ j ∈ Finset.Ico i (N + 2), ((-1 : R) ^ (i + j)) • a i j =
        ((-1 : R) ^ (i + i)) • a i i + ∑ j ∈ Finset.Ico i (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) := by
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.sum_Ico_add' (fun j ↦ ((-1 : R) ^ (i + j)) • a i j) i (N + 1) 1]
    have e3 : ∑ j ∈ Finset.Ico i (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) =
        ((-1 : R) ^ (i + (i + 1))) • a i (i + 1) +
          ∑ j ∈ Finset.Ico (i + 1) (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) :=
      Finset.sum_eq_sum_Ico_succ_bot (by omega) _
    have s1 : ((-1 : R) ^ (i + i)) = 1 := Even.neg_one_pow ⟨i, rfl⟩
    have s2 : ((-1 : R) ^ (i + (i + 1))) = -1 := by rw [← add_assoc, pow_succ, s1]; simp
    rw [← e1, e2, e3, s1, s2, one_smul, neg_smul, one_smul]
    abel
  rw [Finset.sum_congr rfl (fun i hi ↦ row i (by have := Finset.mem_range.1 hi; omega))]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have tL : ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range i, ((-1 : R) ^ (i + j)) • a i j =
      - ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1), ((-1 : R) ^ (k + j)) • b k j := by
    rw [Finset.sum_range_succ', Finset.range_zero, Finset.sum_empty, add_zero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [h1 k j (Finset.mem_range.1 hk) (by have := Finset.mem_range.1 hj; omega), ← neg_smul]
    congr 1
    ring
  have tR : ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.Ico (i + 1) (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) =
      - ∑ k ∈ Finset.range N, ∑ j ∈ Finset.Ico (k + 1) (N + 1), ((-1 : R) ^ (k + j)) • b k j := by
    rw [Finset.sum_range_succ, Finset.Ico_self, Finset.sum_empty, add_zero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have := Finset.mem_Ico.1 hj
    rw [h2 k j (Finset.mem_range.1 hk) (by omega) (by omega), ← neg_smul]
    congr 1
    ring
  have tD : ∑ i ∈ Finset.range (N + 1), (a i i - a i (i + 1)) = a 0 0 - a N (N + 1) := by
    rw [Finset.sum_range_succ, Finset.sum_congr rfl (fun k hk ↦ by rw [h3 k (Finset.mem_range.1 hk)]),
      Finset.sum_range_sub' (fun i ↦ a i i)]
    abel
  have tS : ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (N + 1), ((-1 : R) ^ (k + j)) • b k j =
      ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1), ((-1 : R) ^ (k + j)) • b k j +
        ∑ k ∈ Finset.range N, ∑ j ∈ Finset.Ico (k + 1) (N + 1), ((-1 : R) ^ (k + j)) • b k j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have := Finset.mem_range.1 hk
    exact (Finset.sum_range_add_sum_Ico _ (by omega)).symm
  rw [tL, tR, tD, tS]
  abel

section

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem val_sI {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 1 + 1)) :
    ((sI i t : Fin (1 + 1)) : ℕ) = if i.1 < t.1 then 1 else 0 := by
  show (((if i.castSucc < t then 1 else 0 : Fin (1 + 1))) : ℕ) = _
  by_cases h : i.1 < t.1
  · rw [if_pos (show i.castSucc < t from h), if_pos h]; rfl
  · rw [if_neg (show ¬ i.castSucc < t from h), if_neg h]; rfl

theorem val_pa {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 1 + 1)) :
    ((Fin.predAboveOrderHom i t : Fin (n + 1)) : ℕ) = if i.1 < t.1 then t.1 - 1 else t.1 := by
  show ((Fin.predAbove i t : Fin (n + 1)) : ℕ) = _
  rw [Fin.predAbove]
  by_cases h : i.1 < t.1
  · rw [dite_eq_left (show i.castSucc < t from h), if_pos h]; simp
  · rw [dite_eq_right (show ¬ i.castSucc < t from h), if_neg h]; simp

def aT {n : ℕ} (w : Cn (box F) (n + 1)) (i j : ℕ) : Bi F 1 (n + 1) :=
  if h : i < n + 2 ∧ j < n + 3 then
    bv F ((sI (⟨i, h.1⟩ : Fin (n + 1 + 1))).comp (dl (⟨j, h.2⟩ : Fin (n + 1 + 1 + 1))))
      ((Fin.predAboveOrderHom (⟨i, h.1⟩ : Fin (n + 1 + 1))).comp (dl (⟨j, h.2⟩ : Fin (n + 1 + 1 + 1)))) w
  else 0

def bT {n : ℕ} (w : Cn (box F) (n + 1)) (k j : ℕ) : Bi F 1 (n + 1) :=
  if h : k < n + 1 ∧ j < n + 2 then
    bv F (sI (⟨k, h.1⟩ : Fin (n + 1)))
      ((dl (⟨j, h.2⟩ : Fin (n + 1 + 1))).comp (Fin.predAboveOrderHom (⟨k, h.1⟩ : Fin (n + 1)))) w
  else 0

variable {F}

theorem prism_term_lower_index {n : ℕ} (w : Cn (box F) (n + 1)) (k j : ℕ) (hk : k < n + 1) (hj : j ≤ k) :
    aT F w (k + 1) j = bT F w k j := by
  rw [aT, bT, dite_eq_left (by omega), dite_eq_left (by omega)]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl]
    grind

theorem prism_term_upper_index {n : ℕ} (w : Cn (box F) (n + 1)) (k j : ℕ) (hk : k < n + 1) (hkj : k < j) (hj : j < n + 2) :
    aT F w k (j + 1) = bT F w k j := by
  rw [aT, bT, dite_eq_left (by omega), dite_eq_left (by omega)]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl]
    grind

theorem prism_term_diagonal_equality {n : ℕ} (w : Cn (box F) (n + 1)) (k : ℕ) (hk : k < n + 1) :
    aT F w k (k + 1) = aT F w (k + 1) (k + 1) := by
  rw [aT, aT, dite_eq_left (by omega), dite_eq_left (by omega)]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl]
    grind

theorem aT_first {n : ℕ} (w : Cn (box F) (n + 1)) : aT F w 0 0 = prA F (dl 0) (S0 F (n + 1) w) := by
  rw [aT, dite_eq_left (by omega), S0, prA_bv]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl, cst_apply, Fin.val_zero]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl, Fin.val_zero, OrderHom.id_coe, id_eq]
    grind

theorem aT_last {n : ℕ} (w : Cn (box F) (n + 1)) :
    aT F w (n + 1) (n + 2) = prA F (dl 1) (S0 F (n + 1) w) := by
  rw [aT, dite_eq_left (by omega), S0, prA_bv]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl, cst_apply, Fin.val_zero, Fin.val_one]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl, OrderHom.id_coe, id_eq]
    grind

theorem Sh_dn_expand {n : ℕ} (w : Cn (box F) (n + 1)) :
    Sh F (n + 1) (dn (box F) (n + 1) w) =
      ∑ i ∈ Finset.range (n + 1 + 1), ∑ j ∈ Finset.range (n + 1 + 2), ((-1 : R) ^ (i + j)) • aT F w i j := by
  rw [dn_eq (n + 1)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_range, Sh, LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_sum,
    map_smul, bv_pr, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [aT, dite_eq_left ⟨i.2, j.2⟩, pow_add, mul_comm]

theorem prB_Sh_expand {n : ℕ} (w : Cn (box F) (n + 1)) :
    ∑ j : Fin (n + 1 + 1), ((-1 : R) ^ (j : ℕ)) • prB F (dl j) (Sh F n w) =
      ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1 + 1), ((-1 : R) ^ (k + j)) • bT F w k j := by
  simp only [Finset.sum_range]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Sh, LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_sum, map_smul, prB_bv]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [bT, dite_eq_left ⟨k.2, j.2⟩, smul_smul, pow_add, mul_comm]

theorem shuffle_coboundary_prism_identity {n : ℕ} (w : Cn (box F) (n + 1)) :
    Sh F (n + 1) (dn (box F) (n + 1) w) = prA F (dl 0) (S0 F (n + 1) w) - prA F (dl 1) (S0 F (n + 1) w) -
      ∑ j : Fin (n + 1 + 1), ((-1 : R) ^ (j : ℕ)) • prB F (dl j) (Sh F n w) := by
  rw [Sh_dn_expand, prB_Sh_expand, ← aT_first, ← aT_last]
  exact prism_sum (n + 1) (aT F w) (bT F w) (fun k j hk hj ↦ prism_term_lower_index w k j hk hj)
    (fun k j hk hkj hj ↦ prism_term_upper_index w k j hk hkj hj) (fun k hk ↦ prism_term_diagonal_equality w k hk)

end

theorem Sh_dn : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (w : Cn (box F) (n + 1)), Sh F (n + 1) (dn (box F) (n + 1) w) = prA F (dl 0) (S0 F (n + 1) w) - prA F (dl 1) (S0 F (n + 1) w) - ∑ j : Fin (n + 1 + 1), ((-1 : R) ^ (j : ℕ)) • prB F (dl j) (Sh F n w) :=
  fun _ _ w ↦ shuffle_coboundary_prism_identity w

end GlobalTheory.CompanionTheory.HopfC.Prism
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCup1FormulaPositiveDegree
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.ShMul

theorem val_predAbove {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 1 + 1)) :
    ((Fin.predAboveOrderHom i t : Fin (n + 1)) : ℕ) = if i.1 < t.1 then t.1 - 1 else t.1 := by
  show ((Fin.predAbove i t : Fin (n + 1)) : ℕ) = _
  rw [Fin.predAbove]
  split_ifs with h₁ h₂ h₂
  · simp
  · exact absurd (by simpa [Fin.lt_def] using h₁) h₂
  · exact absurd (by simpa [Fin.lt_def] using h₂) h₁
  · simp

theorem val_sI {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 1 + 1)) :
    ((sI i t : Fin (1 + 1)) : ℕ) = if i.1 < t.1 then 1 else 0 := by
  show ((if i.castSucc < t then (1 : Fin (1 + 1)) else 0 : Fin (1 + 1)) : ℕ) = _
  by_cases h : i.1 < t.1
  · rw [if_pos (by simpa [Fin.lt_def] using h), if_pos h]; rfl
  · rw [if_neg (by simpa [Fin.lt_def] using h), if_neg h]; rfl

theorem shuffle_cup1_product_formula {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (n : ℕ)
    (u : Cn (box F) 1) (w : Cn (box F) (n + 1)) :
    Sh F (n + 1) (cup1 (box F) (n + 1) u w) =
      bv F OrderHom.id (cst 1 0) u * bv F (cst (n + 1) 1) OrderHom.id w -
        bv F (cst 1 0) (fr n) u * prB F (dl 0) (Sh F n w) := by
  have a1 : bv F (sI (0 : Fin (n + 1 + 1))) (Fin.predAboveOrderHom 0) (pr (box F) (fr (n + 1)) u) =
      bv F OrderHom.id (cst 1 0) u := by
    rw [bv_pr]
    refine bv_congr ?_ ?_ u
    · intro t
      apply Fin.ext
      simp only [OrderHom.comp, OrderHom.coe_mk, Function.comp_apply, val_sI, val_predAbove]
      change (if 0 < t.val then 1 else 0) = t.val
      have ht := t.isLt
      split_ifs <;> omega
    · intro t
      apply Fin.ext
      simp only [OrderHom.comp, OrderHom.coe_mk, Function.comp_apply, val_sI, val_predAbove]
      change (if 0 < t.val then t.val - 1 else t.val) = 0
      have ht := t.isLt
      split_ifs <;> omega
  have a2 : bv F (sI (0 : Fin (n + 1 + 1))) (Fin.predAboveOrderHom 0) (pr (box F) (dl 0) w) =
      bv F (cst (n + 1) 1) OrderHom.id w := by
    rw [bv_pr]
    refine bv_congr ?_ ?_ w
    · intro t
      apply Fin.ext
      simp only [OrderHom.comp, OrderHom.coe_mk, Function.comp_apply, val_sI, val_predAbove]
      change (if 0 < t.val + 1 then 1 else 0) = 1
      have ht := t.isLt
      split_ifs <;> omega
    · intro t
      apply Fin.ext
      simp only [OrderHom.comp, OrderHom.coe_mk, Function.comp_apply, val_sI, val_predAbove]
      change (if 0 < t.val + 1 then t.val + 1 - 1 else t.val + 1) = t.val
      have ht := t.isLt
      split_ifs <;> omega
  have b1 : ∀ j : Fin (n + 1), bv F (sI j.succ) (Fin.predAboveOrderHom j.succ) (pr (box F) (fr (n + 1)) u) =
      bv F (cst 1 0) (fr n) u := fun j ↦ by
    rw [bv_pr]
    refine bv_congr ?_ ?_ u
    · intro t
      apply Fin.ext
      simp only [OrderHom.comp, OrderHom.coe_mk, Function.comp_apply, val_sI, val_predAbove]
      change (if j.val + 1 < t.val then 1 else 0) = 0
      have ht := t.isLt
      split_ifs <;> omega
    · intro t
      apply Fin.ext
      simp only [OrderHom.comp, OrderHom.coe_mk, Function.comp_apply, val_sI, val_predAbove]
      change (if j.val + 1 < t.val then t.val - 1 else t.val) = t.val
      have ht := t.isLt
      split_ifs <;> omega
  have b2 : ∀ j : Fin (n + 1), bv F (sI j.succ) (Fin.predAboveOrderHom j.succ) (pr (box F) (dl 0) w) =
      prB F (dl 0) (bv F (sI j) (Fin.predAboveOrderHom j) w) := fun j ↦ by
    rw [bv_pr, prB_bv]
    refine bv_congr ?_ ?_ w
    · intro t
      apply Fin.ext
      simp only [OrderHom.comp, OrderHom.coe_mk, Function.comp_apply, val_sI, val_predAbove]
      change (if j.val + 1 < t.val + 1 then 1 else 0) = (if j.val < t.val then 1 else 0)
      have ht := t.isLt
      split_ifs <;> omega
    · intro t
      apply Fin.ext
      simp only [OrderHom.comp, OrderHom.coe_mk, Function.comp_apply, val_sI, val_predAbove]
      change (if j.val + 1 < t.val + 1 then t.val + 1 - 1 else t.val + 1) = (j.predAboveOrderHom t).succ.val
      rw [Fin.val_succ, val_predAbove]
      have ht := t.isLt
      split_ifs <;> omega
  simp only [Sh, LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, cup1_apply, map_mul, map_sum,
    map_smul]
  rw [Fin.sum_univ_succ]
  simp only [a1, a2, b1, b2, Fin.val_zero, pow_zero, one_smul, Fin.val_succ, Finset.mul_sum, mul_smul_comm]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [pow_succ]

end GlobalTheory.CompanionTheory.HopfC.ShMul
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateShafarevichTransport
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso ReciprocityTheory.Neutral.Bridge

namespace GlobalTheory.CompanionTheory.PTIso.ShaTransfer

theorem nonempty_equiv_of_mem_iff {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (e : A ≃ₗ[R] B) (p : Submodule R A) (q : Submodule R B)
    (h : ∀ x, x ∈ p ↔ e x ∈ q) : Nonempty (p ≃ₗ[R] q) := by
  refine ⟨LinearEquiv.ofSubmodules e p q ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).1 hx
  · intro hy
    exact ⟨e.symm y, (h _).2 (by simpa using hy), by simp⟩

theorem dualData_transfer {R A B A' B' : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    (eA : A' ≃ₗ[R] A) (eB : B' ≃ₗ[R] B)
    (h : Finite A' ∧ Finite B' ∧ Nonempty (B' ≃ₗ[R] Module.Dual R A') ∧
      Nat.card A' = Nat.card B') :
    Finite A ∧ Finite B ∧ Nonempty (B ≃ₗ[R] Module.Dual R A) ∧ Nat.card A = Nat.card B := by
  obtain ⟨hA, hB, ⟨f⟩, hc⟩ := h
  refine ⟨Finite.of_equiv _ eA.toEquiv, Finite.of_equiv _ eB.toEquiv,
    ⟨(eB.symm.trans f).trans eA.symm.dualMap⟩, ?_⟩
  rw [← Nat.card_congr eA.toEquiv, ← Nat.card_congr eB.toEquiv, hc]

section Rep

variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
  {I I' : Type} {D : I → Type} {D' : I' → Type}
  [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)]
  (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i))
  (φ' : ∀ i, D' i →* Γ') (hφ' : ∀ i, Continuous (φ' i))
  {N : Type} [AddCommGroup N] [Module R N] [TopologicalSpace N] [DiscreteTopology N]
  (σ : Representation R Γ N) (σ' : Representation R Γ' N)
  (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i))

theorem local_compat (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) (i : I) :
    ∀ d m, (σ'.comp (φ' (eI i))) (eD i d) m = (σ.comp (φ i)) d m := by
  intro d m
  show σ' (φ' (eI i) (eD i d)) m = σ (φ i d) m
  rw [hD, hσ]

theorem res_h1_iso_h1 (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) (i : I) (x : H1 σ') :
    resH1 σ (φ i) (hφ i) (equivH1OfIso eG σ' σ hσ x) =
      equivH1OfIso (eD i) (σ'.comp (φ' (eI i))) (σ.comp (φ i)) (local_compat φ φ' σ σ' eG eI eD hD hσ i)
        (resH1 σ' (φ' (eI i)) (hφ' (eI i)) x) := by
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    funext d
    show f.1 (eG (φ i d)) = f.1 (φ' (eI i) (eD i d))
    rw [hD]

theorem res_h2_iso_h2 (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) (i : I) (x : H2 σ') :
    resH2 σ (φ i) (hφ i) (equivH2OfIso eG σ' σ hσ x) =
      equivH2OfIso (eD i) (σ'.comp (φ' (eI i))) (σ.comp (φ i)) (local_compat φ φ' σ σ' eG eI eD hD hσ i)
        (resH2 σ' (φ' (eI i)) (hφ' (eI i)) x) := by
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    funext d
    show f.1 (eG (φ i d.1), eG (φ i d.2)) = f.1 (φ' (eI i) (eD i d.1), φ' (eI i) (eD i d.2))
    rw [hD, hD]

theorem mem_Sha1_iff_equiv_mem (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) (x : H1 σ') :
    x ∈ Sha1 σ' φ' hφ' ↔ equivH1OfIso eG σ' σ hσ x ∈ Sha1 σ φ hφ := by
  simp only [Sha1, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h i
    rw [res_h1_iso_h1 φ hφ φ' hφ' σ σ' eG eI eD hD hσ, h, map_zero]
  · intro h i'
    obtain ⟨i, rfl⟩ := eI.surjective i'
    have hi := h i
    rw [res_h1_iso_h1 φ hφ φ' hφ' σ σ' eG eI eD hD hσ] at hi
    exact (LinearEquiv.map_eq_zero_iff _).1 hi

theorem mem_Sha2_iff_equiv_mem (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) (x : H2 σ') :
    x ∈ Sha2 σ' φ' hφ' ↔ equivH2OfIso eG σ' σ hσ x ∈ Sha2 σ φ hφ := by
  simp only [Sha2, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h i
    rw [res_h2_iso_h2 φ hφ φ' hφ' σ σ' eG eI eD hD hσ, h, map_zero]
  · intro h i'
    obtain ⟨i, rfl⟩ := eI.surjective i'
    have hi := h i
    rw [res_h2_iso_h2 φ hφ φ' hφ' σ σ' eG eI eD hD hσ] at hi
    exact (LinearEquiv.map_eq_zero_iff _).1 hi

theorem nonempty_sha1_equiv (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) :
    Nonempty (Sha1 σ' φ' hφ' ≃ₗ[R] Sha1 σ φ hφ) :=
  nonempty_equiv_of_mem_iff (equivH1OfIso eG σ' σ hσ) _ _
    (mem_Sha1_iff_equiv_mem φ hφ φ' hφ' σ σ' eG eI eD hD hσ)

theorem nonempty_sha2_equiv (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) :
    Nonempty (Sha2 σ' φ' hφ' ≃ₗ[R] Sha2 σ φ hφ) :=
  nonempty_equiv_of_mem_iff (equivH2OfIso eG σ' σ hσ) _ _
    (mem_Sha2_iff_equiv_mem φ hφ φ' hφ' σ σ' eG eI eD hD hσ)

end Rep

theorem twDual_compat_of_iso {R Γ Γ' M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [Group Γ'] [TopologicalSpace Γ'] [AddCommGroup M] [Module R M]
    (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ) (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
    (eG : Γ ≃ₜ* Γ') (hχ : ∀ g, χ' (eG g) = χ g) (hρ : ∀ g m, ρ' (eG g) m = ρ g m) :
    ∀ g ψ, twDual χ' ρ' (eG g) ψ = twDual χ ρ g ψ := by
  intro g ψ
  refine DFunLike.ext _ _ fun m => ?_
  rw [twDual_apply, twDual_apply, hχ, ← map_inv, hρ]

theorem shaG_transfer {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
    {I I' : Type} [Fintype I] [Fintype I'] {D : I → Type} {D' : I' → Type}
    [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
    [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)]
    (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i))
    (φ' : ∀ i, D' i →* Γ') (hφ' : ∀ i, Continuous (φ' i))
    (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ)
    {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
    (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i))
    (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hχ : ∀ g, χ' (eG g) = χ g) (hρ : ∀ g m, ρ' (eG g) m = ρ g m)
    (h : ShaG φ' hφ' χ' ρ') : ShaG φ hφ χ ρ := by
  have hT := twDual_compat_of_iso χ χ' ρ ρ' eG hχ hρ
  obtain ⟨a1⟩ := nonempty_sha1_equiv φ hφ φ' hφ' ρ ρ' eG eI eD hD hρ
  obtain ⟨a2⟩ := nonempty_sha2_equiv φ hφ φ' hφ' ρ ρ' eG eI eD hD hρ
  obtain ⟨b1⟩ := nonempty_sha1_equiv φ hφ φ' hφ' (twDual χ ρ) (twDual χ' ρ') eG eI eD hD hT
  obtain ⟨b2⟩ := nonempty_sha2_equiv φ hφ φ' hφ' (twDual χ ρ) (twDual χ' ρ') eG eI eD hD hT
  exact ⟨dualData_transfer b1 a2 h.1, dualData_transfer a1 b2 h.2⟩

end GlobalTheory.CompanionTheory.PTIso.ShaTransfer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorSpaceHasBasisOfDimension
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem vb_basis_of_isField {R : Type} [CommRing R] (hR : IsField R) {M : Type} [AddCommGroup M] [Module R M]
    (g : ℕ) (h : VB R M g) : Nonempty (Module.Basis (Fin g) R M) := by
  obtain ⟨hfin, -, hrank⟩ := h
  haveI : Module.Free R M := by
    letI := hR.toField
    exact Module.Free.of_divisionRing R M
  haveI : Nontrivial R := ⟨hR.exists_pair_ne⟩
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  have hg : Module.finrank R M = g := by
    have hp := hrank p
    rw [Module.rankAtStalk_eq_finrank_of_free] at hp
    exact hp
  exact ⟨Module.finBasisOfFinrankEq R M hg⟩

end GlobalTheory.CompanionTheory.HopfC
end

