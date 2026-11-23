module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.StrongApproximationSLElementary
section
open Matrix

namespace GroundTheory.Automorphic

variable {n : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable (n) (R : Type*) [CommRing R]

def transvectionGL (t : TransvectionStruct n R) : GL n R where
  val := t.toMatrix
  inv := t.inv.toMatrix
  val_inv := TransvectionStruct.mul_inv t
  inv_val := TransvectionStruct.inv_mul t

@[simp]
theorem coe_transvectionGL (t : TransvectionStruct n R) :
    (transvectionGL n R t : Matrix n n R) = t.toMatrix := rfl

def elementarySubgroup : Subgroup (GL n R) :=
  Subgroup.closure (Set.range (transvectionGL n R))

variable {n R}

theorem transvectionGL_mem_elementarySubgroup (t : TransvectionStruct n R) :
    transvectionGL n R t ∈ elementarySubgroup n R :=
  Subgroup.subset_closure ⟨t, rfl⟩

theorem elementarySubgroup_le_ker_det :
    elementarySubgroup n R ≤ (Matrix.GeneralLinearGroup.det : GL n R →* Rˣ).ker := by
  rw [elementarySubgroup, Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, TransvectionStruct.det]

theorem coe_list_prod_transvectionGL (L : List (TransvectionStruct n R)) :
    (((L.map (transvectionGL n R)).prod : GL n R) : Matrix n n R) =
      (L.map TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => simp
  | cons t L ih => simp [ih]

theorem list_prod_transvectionGL_mem (L : List (TransvectionStruct n R)) :
    (L.map (transvectionGL n R)).prod ∈ elementarySubgroup n R :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
    exact transvectionGL_mem_elementarySubgroup t

theorem mul_transvection_apply (i j : n) (c : R) (M : Matrix n n R) (a b : n) :
    (M * transvection i j c) a b = if b = j then M a j + c * M a i else M a b := by
  split_ifs with h
  · subst h
    exact mul_transvection_apply_same i b a c M
  · exact mul_transvection_apply_of_ne i j a b h c M

theorem transvection_mul_eq_diagonal_update (i j : n) (hij : i ≠ j) (u : Rˣ) :
    transvection i j (u : R) * transvection j i (-(↑u⁻¹ : R)) * transvection i j (u : R) *
      transvection i j (-1) * transvection j i 1 * transvection i j (-1) =
      diagonal (Function.update (Function.update (1 : n → R) i u) j (↑u⁻¹ : R)) := by
  ext a b
  simp only [mul_transvection_apply]
  simp only [diagonal_apply, Function.update_apply, Pi.one_apply, transvection, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hbj : b = j <;> by_cases hbi : b = i <;> by_cases hai : a = i <;> by_cases haj : a = j <;>
    simp [hbj, hbi, hai, haj, hij, Ne.symm hij, @eq_comm _ i, @eq_comm _ j]
  all_goals (try ring_nf)
  all_goals (try simp)

def diagonalGL : (n → Rˣ) →* GL n R where
  toFun d :=
    { val := diagonal fun k => (d k : R)
      inv := diagonal fun k => (↑(d k)⁻¹ : R)
      val_inv := by simp [diagonal_mul_diagonal]
      inv_val := by simp [diagonal_mul_diagonal] }
  map_one' := by ext1; simp
  map_mul' d e := by ext1; simp [diagonal_mul_diagonal]

@[simp]
theorem coe_diagonalGL (d : n → Rˣ) :
    (diagonalGL d : Matrix n n R) = diagonal fun k => (d k : R) := rfl

theorem diagonal_update_mem_elementarySubgroup (i j : n) (hij : i ≠ j) (u : Rˣ) :
    diagonalGL (Pi.mulSingle i u * Pi.mulSingle j u⁻¹) ∈ elementarySubgroup n R := by
  have h : diagonalGL (Pi.mulSingle i u * Pi.mulSingle j u⁻¹) =
      transvectionGL n R ⟨i, j, hij, u⟩ * transvectionGL n R ⟨j, i, hij.symm, -(↑u⁻¹ : R)⟩ *
        transvectionGL n R ⟨i, j, hij, u⟩ * transvectionGL n R ⟨i, j, hij, -1⟩ *
          transvectionGL n R ⟨j, i, hij.symm, 1⟩ * transvectionGL n R ⟨i, j, hij, -1⟩ := by
    ext1
    simp only [Units.val_mul, coe_transvectionGL, TransvectionStruct.toMatrix_mk, coe_diagonalGL]
    rw [transvection_mul_eq_diagonal_update i j hij u]
    congr 1
    funext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all
  rw [h]
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_ <;>
    exact transvectionGL_mem_elementarySubgroup _

theorem diagonalGL_mem_elementarySubgroup {d : n → Rˣ} (hd : ∏ k, d k = 1) :
    diagonalGL d ∈ elementarySubgroup n R := by
  classical
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · have : d = 1 := funext fun k => isEmptyElim k
    rw [this, map_one]
    exact one_mem _
  have hmem : ∀ i ∈ Finset.univ.erase i₀,
      Pi.mulSingle i (d i) * Pi.mulSingle i₀ (d i)⁻¹ ∈
        (elementarySubgroup n R).comap (diagonalGL (n := n) (R := R)) := fun i hi =>
    diagonal_update_mem_elementarySubgroup i i₀ (Finset.ne_of_mem_erase hi) (d i)
  have hprod := Subgroup.prod_mem _ hmem
  have heq : ∏ i ∈ Finset.univ.erase i₀, (Pi.mulSingle i (d i) * Pi.mulSingle i₀ (d i)⁻¹) = d := by
    funext k
    rw [Finset.prod_apply]
    simp only [Pi.mul_apply, Pi.mulSingle_apply]
    by_cases hk : k = i₀
    · subst hk
      have h1 : ∀ i ∈ Finset.univ.erase k,
          ((if k = i then d i else 1) * if k = k then (d i)⁻¹ else 1) = (d i)⁻¹ := by
        intro i hi
        rw [if_neg (Finset.ne_of_mem_erase hi).symm, if_pos rfl, one_mul]
      rw [Finset.prod_congr rfl h1, Finset.prod_inv_distrib]
      have h2 := Finset.mul_prod_erase Finset.univ d (Finset.mem_univ k)
      rw [hd] at h2
      rw [eq_comm, ← mul_eq_one_iff_eq_inv]
      exact h2
    · have h1 : ∀ i ∈ Finset.univ.erase i₀,
          ((if k = i then d i else 1) * if k = i₀ then (d i)⁻¹ else 1) =
            if k = i then d i else 1 := by
        intro i _
        rw [if_neg hk, mul_one]
      rw [Finset.prod_congr rfl h1, Finset.prod_ite_eq]
      rw [if_pos (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)]
  rw [heq] at hprod
  exact hprod

end CommRing

section Field

variable {F : Type*} [Field F]

theorem mem_elementarySubgroup_of_det_eq_one {g : GL n F}
    (hg : Matrix.GeneralLinearGroup.det g = 1) : g ∈ elementarySubgroup n F := by
  classical
  obtain ⟨L, L', D, hM⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (g : Matrix n n F)
  have hdet : ∏ k, D k = 1 := by
    have h1 : (g : Matrix n n F).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hg, Units.val_one]
    rw [hM, det_mul, det_mul, TransvectionStruct.det_toMatrix_prod,
      TransvectionStruct.det_toMatrix_prod, det_diagonal, one_mul, mul_one] at h1
    exact h1
  have hD : ∀ k, D k ≠ 0 := fun k h0 => by
    have := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [hdet] at this
    exact one_ne_zero this
  let d : n → Fˣ := fun k => Units.mk0 (D k) (hD k)
  have hd : ∏ k, d k = 1 := by
    ext
    simp [d, Units.coe_prod, hdet]
  have hg' : g = (L.map (transvectionGL n F)).prod * diagonalGL d *
      (L'.map (transvectionGL n F)).prod := by
    ext1
    simp only [Units.val_mul, coe_list_prod_transvectionGL, coe_diagonalGL]
    rw [hM]
    rfl
  rw [hg']
  exact mul_mem (mul_mem (list_prod_transvectionGL_mem L) (diagonalGL_mem_elementarySubgroup hd))
    (list_prod_transvectionGL_mem L')

end Field

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.WhittakerRelevance
section
namespace GroundTheory.Automorphic

namespace Whittaker

open Finset

variable {n : ℕ} {w : Equiv.Perm (Fin n)}

theorem val_eq_of_le_of_le
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) :
    ∀ (g : ℕ) (z y : Fin n), (w y).val = (w z).val + g → z ≤ y →
      ∀ x : Fin n, z ≤ x → x ≤ y → (w x).val = (w z).val + (x.val - z.val) := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro z y hgap hzy x hzx hxy
  rw [Fin.le_iff_val_le_val] at hzy hzx hxy
  rcases Nat.eq_zero_or_pos g with hg | hg
  · subst hg
    have hyz : y = z := w.injective (Fin.ext (by omega))
    subst hyz
    have hxy' : x = y := Fin.ext (by omega)
    subst hxy'
    simp
  · have hlt : (w z).val + 1 < n := by have := (w y).isLt; omega
    set p := w.symm ⟨(w z).val + 1, hlt⟩ with hp
    have hwp : (w p).val = (w z).val + 1 := by simp [hp]
    have hzy' : z.val < y.val := by
      rcases Nat.lt_or_eq_of_le hzy with h | h
      · exact h
      · have : z = y := Fin.ext h
        subst this
        omega
    rcases lt_trichotomy p.val z.val with hpz | hpz | hpz
    ·
      exfalso
      have key := ih (g - 1) (by omega) p y (by omega) (Fin.le_iff_val_le_val.2 (by omega)) z
        (Fin.le_iff_val_le_val.2 (by omega)) (Fin.le_iff_val_le_val.2 hzy)
      omega
    · exfalso
      have : p = z := Fin.ext hpz
      rw [this] at hwp
      omega
    ·
      have hp1 : p.val = z.val + 1 := hB z p (Fin.lt_def.2 hpz) hwp
      rcases Nat.eq_or_lt_of_le hzx with hx | hx
      · have : x = z := Fin.ext hx.symm
        subst this
        simp
      · have key := ih (g - 1) (by omega) p y (by omega) (Fin.le_iff_val_le_val.2 (by omega)) x
          (Fin.le_iff_val_le_val.2 (by omega)) (Fin.le_iff_val_le_val.2 hxy)
        omega

theorem val_eq_of_le_right
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b x : Fin n)
    (hbx : b ≤ x) (hx : x.val ≤ b.val + #(univ.filter fun y : Fin n => b < y ∧ w b < w y)) :
    (w x).val = (w b).val + (x.val - b.val) := by
  set R := univ.filter fun y : Fin n => b < y ∧ w b < w y with hR
  by_cases hne : R.Nonempty
  · set m := R.max' hne
    have hm : m ∈ R := R.max'_mem hne
    rw [hR, mem_filter] at hm
    have hsub : R ⊆ Ioc b m := by
      intro y hy
      have hy' := hy
      rw [hR, mem_filter] at hy'
      exact mem_Ioc.2 ⟨hy'.2.1, R.le_max' y hy⟩
    have hcard : #R ≤ m.val - b.val := by
      have := card_le_card hsub
      rwa [Fin.card_Ioc] at this
    have hbm := Fin.lt_def.1 hm.2.1
    have hwbm := Fin.lt_def.1 hm.2.2
    exact val_eq_of_le_of_le hB ((w m).val - (w b).val) b m (by omega) (le_of_lt hm.2.1) x hbx
      (Fin.le_iff_val_le_val.2 (by omega))
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty] at hx
    have : x = b := Fin.ext (by rw [Fin.le_iff_val_le_val] at hbx; omega)
    subst this
    simp

theorem val_add_eq_of_le_left
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b x : Fin n)
    (hxb : x ≤ b) (hx : b.val ≤ x.val + #(univ.filter fun y : Fin n => y < b ∧ w y < w b)) :
    (w x).val + (b.val - x.val) = (w b).val := by
  set L := univ.filter fun y : Fin n => y < b ∧ w y < w b with hL
  by_cases hne : L.Nonempty
  · set m := L.min' hne
    have hm : m ∈ L := L.min'_mem hne
    rw [hL, mem_filter] at hm
    have hsub : L ⊆ Ico m b := by
      intro y hy
      have hy' := hy
      rw [hL, mem_filter] at hy'
      exact mem_Ico.2 ⟨L.min'_le y hy, hy'.2.1⟩
    have hcard : #L ≤ b.val - m.val := by
      have := card_le_card hsub
      rwa [Fin.card_Ico] at this
    have hmb := Fin.lt_def.1 hm.2.1
    have hwmb := Fin.lt_def.1 hm.2.2
    have h1 := val_eq_of_le_of_le hB ((w b).val - (w m).val) m b (by omega) (le_of_lt hm.2.1) x
      (Fin.le_iff_val_le_val.2 (by omega)) hxb
    have h2 := val_eq_of_le_of_le hB ((w b).val - (w m).val) m b (by omega) (le_of_lt hm.2.1) b
      (le_of_lt hm.2.1) le_rfl
    rw [Fin.le_iff_val_le_val] at hxb
    omega
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty] at hx
    have : x = b := Fin.ext (by rw [Fin.le_iff_val_le_val] at hxb; omega)
    subst this
    simp

theorem card_filter_lt_apply (w : Equiv.Perm (Fin n)) (b : Fin n) :
    #(univ.filter fun x : Fin n => w x < w b) = (w b).val := by
  have : (univ.filter fun x : Fin n => w x < w b) = (Iio (w b)).map w.symm.toEmbedding := by
    ext x
    simp [mem_map_equiv]
  rw [this, card_map, Fin.card_Iio]

theorem val_add_card_right (w : Equiv.Perm (Fin n)) (b : Fin n) :
    (w b).val + #(univ.filter fun y : Fin n => b < y ∧ w b < w y) =
      #(univ.filter fun y : Fin n => y < b ∧ w y < w b) + (n - 1 - b.val) := by
  have hIoi : #(univ.filter fun y : Fin n => b < y) = n - 1 - b.val := by
    have : (univ.filter fun y : Fin n => b < y) = Ioi b := by
      ext y
      simp
    rw [this, Fin.card_Ioi]
  rw [← card_filter_lt_apply w b, ← hIoi, card_filter, card_filter, card_filter, card_filter,
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  have hne : y ≠ b → w y ≠ w b := fun h e => h (w.injective e)
  rcases lt_trichotomy y b with h | h | h
  · have h' : ¬ b < y := not_lt.2 (le_of_lt h)
    by_cases hw : w y < w b <;> simp [h, h', hw]
  · subst h
    simp
  · have h' : ¬ y < b := not_lt.2 (le_of_lt h)
    have hyb : w y ≠ w b := hne (ne_of_gt h)
    rcases lt_or_gt_of_ne hyb with hw | hw
    · have hw' : ¬ w b < w y := not_lt.2 (le_of_lt hw)
      simp [h, h', hw, hw']
    · have hw' : ¬ w y < w b := not_lt.2 (le_of_lt hw)
      simp [h, h', hw, hw']

theorem relevant_involution
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b : Fin n) :
    w (Fin.rev (w b)) = Fin.rev b := by
  have hid := val_add_card_right w b
  set r := #(univ.filter fun y : Fin n => b < y ∧ w b < w y)
  set l := #(univ.filter fun y : Fin n => y < b ∧ w y < w b)
  set c := Fin.rev (w b) with hc
  have hcv : c.val = n - (↑(w b) + 1) := by rw [hc, Fin.val_rev]
  have hb := b.isLt
  have hwb := (w b).isLt
  apply Fin.ext
  rw [Fin.val_rev]
  by_cases hcb : b.val ≤ c.val
  · have := val_eq_of_le_right hB b c (Fin.le_iff_val_le_val.2 hcb) (by omega)
    omega
  · have := val_add_eq_of_le_left hB b c (Fin.le_iff_val_le_val.2 (by omega)) (by omega)
    omega

theorem apply_eq_of_run_right {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    (b : Fin n) :
    ∀ k : ℕ, ∀ x : Fin n, x.val = b.val + k →
      k ≤ #(univ.filter fun y : Fin n => b < y ∧ w b < w y) → t (w x) = t (w b) := by
  intro k
  induction k with
  | zero =>
    intro x hx _
    have : x = b := Fin.ext (by omega)
    rw [this]
  | succ k ih =>
    intro x hx hk
    have hxn := x.isLt
    have hk1 : b.val + k < n := by omega
    have h1 := ih ⟨b.val + k, hk1⟩ rfl (by omega)
    have e1 := val_eq_of_le_right hB b x (Fin.le_iff_val_le_val.2 (by omega)) (by omega)
    have e2 := val_eq_of_le_right hB b ⟨b.val + k, hk1⟩ (Fin.le_iff_val_le_val.2 (by simp))
      (by simp; omega)
    have hk2 : b.val + k + 1 < n := by omega
    have hnext : (⟨b.val + k + 1, hk2⟩ : Fin n) = x := Fin.ext (by simp; omega)
    have hasc : w ⟨b.val + k, hk1⟩ < w ⟨b.val + k + 1, hk2⟩ := by
      rw [hnext, Fin.lt_def]
      simp only at e2
      omega
    have := ht ⟨b.val + k, hk1⟩ hk2 hasc
    simp only at this
    rw [hnext] at this
    rw [← this, h1]

theorem apply_eq_of_run_left {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    (b : Fin n) :
    ∀ k : ℕ, ∀ x : Fin n, x.val + k = b.val →
      k ≤ #(univ.filter fun y : Fin n => y < b ∧ w y < w b) → t (w x) = t (w b) := by
  intro k
  induction k with
  | zero =>
    intro x hx _
    have : x = b := Fin.ext (by omega)
    rw [this]
  | succ k ih =>
    intro x hx hk
    have hbn := b.isLt
    have hx1 : x.val + 1 < n := by omega
    have h1 := ih ⟨x.val + 1, hx1⟩ (by simp; omega) (by omega)
    have e1 := val_add_eq_of_le_left hB b x (Fin.le_iff_val_le_val.2 (by omega)) (by omega)
    have e2 := val_add_eq_of_le_left hB b ⟨x.val + 1, hx1⟩ (Fin.le_iff_val_le_val.2 (by simp; omega))
      (by simp; omega)
    have hasc : w x < w ⟨x.val + 1, hx1⟩ := by
      rw [Fin.lt_def]
      simp only at e2
      omega
    have := ht x hx1 hasc
    rw [this]
    exact h1

theorem relevant_torus {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    (b : Fin n) : t (w b) = t (Fin.rev b) := by
  have hid := val_add_card_right w b
  rw [← relevant_involution hB b]
  set c := Fin.rev (w b) with hc
  have hcv : c.val = n - (↑(w b) + 1) := by rw [hc, Fin.val_rev]
  have hb := b.isLt
  have hwb := (w b).isLt
  by_cases hcb : b.val ≤ c.val
  · exact (apply_eq_of_run_right t hB ht b (c.val - b.val) c (by omega) (by omega)).symm
  · exact (apply_eq_of_run_left t hB ht b (b.val - c.val) c (by omega) (by omega)).symm

end Whittaker

end GroundTheory.Automorphic
end

