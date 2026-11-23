module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HermitianFormLiftVecFirstVector
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0014

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HermExpand
section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

theorem herm_conj {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (v w : Fin n → ℂ) :
    star (herm H v w) = herm H w v := by
  have h : ∀ i j, star (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    simpa [Matrix.conjTranspose_apply] using this
  unfold herm
  simp only [dotProduct, mulVec, star_sum, star_mul', star_star, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h]; ring

theorem dot_bvec_r {n : ℕ} (i : Fin n) (x : Fin n → ℂ) : x ⬝ᵥ bvec i = x i := by
  simp [bvec]

section ex
variable (k n : ℕ)

def wp (i : Fin (k - 1)) : Fin (2 * n + k + 1) := wI k n ⟨i.val + 1, by omega⟩

def wv (i : Fin (k - 1)) : Fin (2 * n + k + 1) → ℂ := bvec (wp k n i)

theorem wp_val (i : Fin (k - 1)) : (wp k n i).val = n + (i.val + 1) := rfl

private theorem Hpk_apply_wp_eq_ite (i : Fin (k - 1)) (j : Fin (2 * n + k + 1)) :
    Hpk k n (wp k n i) j = if wp k n i = j then 1 else 0 := by
  have hi := i.isLt
  have hv := wp_val k n i
  have hj := j.isLt
  have hij : wp k n i = j ↔ (wp k n i).val = j.val := Fin.ext_iff
  unfold Hpk
  by_cases h : (wp k n i).val = j.val
  · rw [if_pos (hij.2 h), if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, hij.2 h⟩,
      if_neg (by omega)]
  · rw [if_neg (fun he => h (hij.1 he)), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem hpk_mv_w (i : Fin (k - 1)) (y : Fin (2 * n + k + 1) → ℂ) : (Hpk k n *ᵥ y) (wp k n i) = y (wp k n i) := by
  simp only [mulVec, dotProduct, Hpk_apply_wp_eq_ite, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem hpk_bvec_w (i : Fin (k - 1)) : Hpk k n *ᵥ wv k n i = wv k n i := by
  funext p
  have hc : Hpk k n p (wp k n i) = star (Hpk k n (wp k n i) p) := by
    have := congrFun (congrFun (hpk_conjT k n) p) (wp k n i)
    rw [Matrix.conjTranspose_apply] at this
    exact this.symm
  simp only [wv, bvec, mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hc, Hpk_apply_wp_eq_ite]
  by_cases h : wp k n i = p
  · subst h; simp
  · rw [if_neg h, if_neg (fun he => h he.symm), star_zero]

theorem phi_w (a : Fin (n + 1)) (i : Fin (k - 1)) : phiV k n a (wp k n i) = 0 := by
  have hi := i.isLt
  have hv := wp_val k n i
  have ha := a.isLt
  unfold phiV
  split_ifs with h
  · simp only [bvec]
    rw [Pi.single_apply, if_neg]
    intro he
    have := congrArg Fin.val he
    simp only [esI] at this
    omega
  · simp only [epsV, bvec, Pi.smul_apply, Pi.add_apply, Pi.single_apply]
    rw [if_neg, if_neg]
    · simp
    · intro he
      have := congrArg Fin.val he
      simp [wI, Fin.val_last] at this <;> omega
    · intro he
      have := congrArg Fin.val he
      simp [wI] at this <;> omega

theorem phi'_w (a : Fin (n + 1)) (i : Fin (k - 1)) : phiV' k n a (wp k n i) = 0 := by
  show (Hpk k n *ᵥ phiV k n a) (wp k n i) = 0
  rw [hpk_mv_w, phi_w]

theorem herm_w_l (v : Fin (2 * n + k + 1) → ℂ) (i : Fin (k - 1)) : herm (Hpk k n) (wv k n i) v = star (v (wp k n i)) := by
  unfold herm
  rw [hpk_bvec_w]
  simp only [wv]
  rw [dot_bvec_r]
  rfl

theorem herm_w_r (v : Fin (2 * n + k + 1) → ℂ) (i : Fin (k - 1)) : herm (Hpk k n) v (wv k n i) = v (wp k n i) := by
  unfold herm
  have hs : star (wv k n i) = Pi.single (wp k n i) (1 : ℂ) := by
    ext j
    by_cases h : j = wp k n i <;> simp [wv, bvec, h]
  rw [hs, single_dotProduct, one_mul, hpk_mv_w]

def Phv : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1)) → Fin (2 * n + k + 1) → ℂ :=
  Sum.elim (phiV' k n) (Sum.elim (phiV k n) (wv k n))

def Psv : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1)) → Fin (2 * n + k + 1) → ℂ :=
  Sum.elim (phiV k n) (Sum.elim (phiV' k n) (wv k n))

private theorem herm_Hpk_mulVec_Hpk_mulVec (x y : Fin (2 * n + k + 1) → ℂ) :
    herm (Hpk k n) (Hpk k n *ᵥ x) (Hpk k n *ᵥ y) = herm (Hpk k n) x y := by
  unfold herm
  rw [mulVec_mulVec, hpk_mul, one_mulVec, Matrix.star_mulVec, hpk_conjT, dotProduct_mulVec]

theorem pair_all (hk : 1 ≤ k) (c d : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1))) :
    herm (Hpk k n) (Phv k n d) (Psv k n c) = if c = d then 1 else 0 := by
  have hφ' : ∀ a, phiV' k n a = Hpk k n *ᵥ phiV k n a := fun _ => rfl
  rcases c with b | b | i <;> rcases d with a | a | j <;>
    simp only [Phv, Psv, Sum.elim_inl, Sum.elim_inr]
  · rw [← herm_conj (Hpk k n) (hpk_conjT k n) (phiV k n b) (phiV' k n a), phi_pair k n hk]
    by_cases h : b = a
    · subst h; simp
    · simp [h]
  · rw [phi_iso k n hk]; simp
  · rw [herm_w_l, phi_w]; simp
  · rw [hφ', hφ', herm_Hpk_mulVec_Hpk_mulVec, phi_iso k n hk]; simp
  · rw [phi_pair k n hk]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  · rw [herm_w_l, phi'_w]; simp
  · rw [herm_w_r, phi'_w]; simp
  · rw [herm_w_r, phi_w]; simp
  · rw [herm_w_l]
    simp only [wv, bvec, Pi.single_apply]
    by_cases h : i = j
    · subst h; simp
    · have hne : wp k n j ≠ wp k n i := by
        intro he
        apply h
        ext
        have := congrArg Fin.val he
        rw [wp_val, wp_val] at this
        omega
      simp [hne, h]

private theorem herm_sum_smul_left_tail_integrals {ι : Type*} [Fintype ι] (g : ι → ℂ) (v : ι → Fin (2 * n + k + 1) → ℂ)
    (w : Fin (2 * n + k + 1) → ℂ) :
    herm (Hpk k n) (∑ c, g c • v c) w = ∑ c, g c * herm (Hpk k n) (v c) w := by
  unfold herm
  simp only [dotProduct, mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem expand (hk : 1 ≤ k) (y : Fin (2 * n + k + 1) → ℂ) :
    y = ∑ c, herm (Hpk k n) y (Psv k n c) • Phv k n c := by
  have hcoef : ∀ (g : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1)) → ℂ) c,
      herm (Hpk k n) (∑ d, g d • Phv k n d) (Psv k n c) = g c := by
    intro g c
    rw [herm_sum_smul_left_tail_integrals]
    simp [pair_all k n hk]
  have hli : LinearIndependent ℂ (Phv k n) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg c
    have := hcoef g c
    rw [hg] at this
    simpa [herm] using this.symm
  have hcard : Fintype.card (Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1))) =
      Module.finrank ℂ (Fin (2 * n + k + 1) → ℂ) := by
    simp only [Fintype.card_sum, Fintype.card_fin, Module.finrank_fin_fun]
    omega
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ∀ c, b c = Phv k n c := fun c => by simp [b]
  have hy := b.sum_repr y
  simp only [hb] at hy
  conv_lhs => rw [← hy]
  refine Finset.sum_congr rfl fun c _ => ?_
  have := hcoef (fun d => b.repr y d) c
  rw [hy] at this
  rw [this]

theorem herm_expand (hk : 1 ≤ k) (y w : Fin (2 * n + k + 1) → ℂ) :
    herm (Hpk k n) y w = ∑ j, (herm (Hpk k n) y (phiV k n j) * herm (Hpk k n) (phiV' k n j) w +
      herm (Hpk k n) y (phiV' k n j) * herm (Hpk k n) (phiV k n j) w) +
      ∑ i, y (wp k n i) * herm (Hpk k n) (wv k n i) w := by
  conv_lhs => rw [expand k n hk y]
  rw [herm_sum_smul_left_tail_integrals, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Psv, Phv, Sum.elim_inl, Sum.elim_inr, herm_w_r]
  rw [Finset.sum_add_distrib]
  exact (add_assoc _ _ _).symm

theorem herm_linF (hk : 1 ≤ k) (y w : Fin (2 * n + k + 1) → ℂ) (s : ℝ) :
    herm (Hpk k n) y w = linF (fun j => herm (Hpk k n) (phiV' k n (Fin.cast (by omega) j)) w)
      (fun j => herm (Hpk k n) (phiV k n (Fin.cast (by omega) j)) w) (fun i => herm (Hpk k n) (wv k n i) w)
      (hcoord k n (y, s)) := by
  rw [herm_expand k n hk y w]
  simp only [linF, hcoord]
  congr 1
  exact ((finCongr (by omega : 1 + n = n + 1)).sum_comp (fun j =>
    herm (Hpk k n) y (phiV k n j) * herm (Hpk k n) (phiV' k n j) w +
      herm (Hpk k n) y (phiV' k n j) * herm (Hpk k n) (phiV k n j) w)).symm

end ex

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HpkMulVecMulVec
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section herm
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)

theorem herm_UH' [DecidableEq ι] {g : Matrix ι ι ℂ} (hg : g ∈ UH H) (u v : ι → ℂ) :
    herm H (g *ᵥ u) (g *ᵥ v) = herm H u v := by
  have hg' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    hg']

theorem herm_sum_l {α : Type*} (c : α → ℂ) (s : Finset α) (u : α → ι → ℂ) (w : ι → ℂ) :
    herm H (∑ j ∈ s, c j • u j) w = ∑ j ∈ s, c j * herm H (u j) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [herm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
      smul_eq_mul]

theorem herm_sum_r {α : Type*} (c : α → ℂ) (s : Finset α) (u : ι → ℂ) (w : α → ι → ℂ) :
    herm H u (∑ j ∈ s, c j • w j) = ∑ j ∈ s, star (c j) * herm H u (w j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [herm, star_add, star_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]

theorem mat_eq_of_mulVec' [DecidableEq ι] {A B : Matrix ι ι ℂ} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  exact Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h v])

end herm

section hpk
variable (k r : ℕ)

theorem hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h]
    simp only [Matrix.mulVec, dotProduct, hpk_out k r h]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro j _ hj
      have hj' : j.val ≠ 2 * r + k - i.val := fun hc => hj (Fin.ext hc)
      simp [hj']
    · simp
  · rw [if_neg h]
    simp only [Matrix.mulVec, dotProduct, hpk_mid k r h]
    rw [Finset.sum_eq_single i]
    · by_cases h2 : i.val = r + k <;> simp [h2]
    · intro j _ hj
      have hj' : j.val ≠ i.val := fun hc => hj (Fin.ext hc)
      simp [hj']
    · simp

theorem hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i
  have hi := i.isLt
  rw [hpk_mulVec]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, hpk_mulVec, if_pos (by dsimp only; omega)]
    congr 1
    ext
    dsimp only
    omega
  · rw [if_neg h]
    split_ifs with h2
    · rw [hpk_mulVec, if_neg h, if_pos h2, neg_neg]
    · rw [hpk_mulVec, if_neg h, if_neg h2]

theorem hpk_sq : Hpk k r * Hpk k r = 1 :=
  mat_eq_of_mulVec' fun v => by rw [← Matrix.mulVec_mulVec, hpk_mulVec_mulVec, Matrix.one_mulVec]

variable {k r}

theorem uh_inv_mul {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hpk_sq]
  rw [Matrix.inv_eq_left_inv hl, hl]

theorem uh_mul_inv {g : Mat k r} (hg : g ∈ GV k r) : g * g⁻¹ = 1 :=
  Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (uh_inv_mul hg))

theorem herm_inv {x : Mat k r} (hx : x ∈ GV k r) (g : Mat k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((x⁻¹ * g) *ᵥ v) w = herm (Hpk k r) (g *ᵥ v) (x *ᵥ w) := by
  rw [← herm_UH' (Hpk k r) hx, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, uh_mul_inv hx,
    Matrix.one_mul]

end hpk

section tri

theorem sub_mul_tri {n m : ℕ} (h : m ≤ n) (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.BlockTriangular id) :
    (A * B).submatrix (Fin.castLE h) (Fin.castLE h) =
      A.submatrix (Fin.castLE h) (Fin.castLE h) * B.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have hemb : ∑ l : Fin m, A (Fin.castLE h i) (Fin.castLE h l) * B (Fin.castLE h l) (Fin.castLE h j) =
      ∑ l ∈ Finset.univ.map (Fin.castLEEmb h), A (Fin.castLE h i) l * B l (Fin.castLE h j) := by
    rw [Finset.sum_map]
    rfl
  rw [hemb]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro l _ hl
  have hlm : m ≤ l.val := by
    by_contra hc
    push_neg at hc
    exact hl (Finset.mem_map.mpr ⟨⟨l.val, hc⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  have hjl : id (Fin.castLE h j) < id l := by
    show (Fin.castLE h j).val < l.val
    have := j.isLt
    simp only [Fin.coe_castLE]
    omega
  rw [hB hjl, mul_zero]

theorem sub_tri_mul {n m : ℕ} (h : m ≤ n) (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.BlockTriangular id) :
    (Bᴴ * A).submatrix (Fin.castLE h) (Fin.castLE h) =
      (B.submatrix (Fin.castLE h) (Fin.castLE h))ᴴ * A.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hemb : ∑ l : Fin m, star (B (Fin.castLE h l) (Fin.castLE h i)) * A (Fin.castLE h l) (Fin.castLE h j) =
      ∑ l ∈ Finset.univ.map (Fin.castLEEmb h), star (B l (Fin.castLE h i)) * A l (Fin.castLE h j) := by
    rw [Finset.sum_map]
    rfl
  rw [hemb]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro l _ hl
  have hlm : m ≤ l.val := by
    by_contra hc
    push_neg at hc
    exact hl (Finset.mem_map.mpr ⟨⟨l.val, hc⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  have hil : id (Fin.castLE h i) < id l := by
    show (Fin.castLE h i).val < l.val
    have := i.isLt
    simp only [Fin.coe_castLE]
    omega
  rw [hB hil, star_zero, zero_mul]

theorem tri_sub {n m : ℕ} (h : m ≤ n) (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.BlockTriangular id) :
    (B.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id :=
  fun i j hij => hB (show (Fin.castLE h j).val < (Fin.castLE h i).val from hij)

end tri

section dl
variable {k r : ℕ}

def Pm (k r : ℕ) (g : Mat k r) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun a b => herm (Hpk k r) (g *ᵥ phiV' k r b) (phiV' k r a)

def cl (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (l : Fin (r + 1)) : ℝ≥0 :=
  ∏ j : Fin (l.val + 1), ‖τ (Fin.castLE (show l.val + 1 ≤ r + 1 by omega) j)
    (Fin.castLE (show l.val + 1 ≤ r + 1 by omega) j)‖₊

theorem dl_eq (l : Fin (r + 1)) (g : Mat k r) :
    Dl k r l g = ((Pm k r g).submatrix (Fin.castLE (show l.val + 1 ≤ r + 1 by omega))
      (Fin.castLE (show l.val + 1 ≤ r + 1 by omega))).det := rfl

theorem pm_left {x κ : Mat k r} (hx : x ∈ GV k r) (hκ : κ ∈ GV k r) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hY : ∀ a, x *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) (g : Mat k r) :
    Pm k r (x⁻¹ * g) = τᴴ * Pm k r (κ⁻¹ * g) := by
  ext a b
  simp only [Pm, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [herm_inv hx, hY a, herm_sum_r]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [herm_inv hκ]

theorem pm_right {y κ : Mat k r} (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hY : ∀ a, y *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) (g : Mat k r) :
    Pm k r (g * y) = Pm k r (g * κ) * τ := by
  ext a b
  simp only [Pm, Matrix.of_apply, Matrix.mul_apply]
  have e : (g * y) *ᵥ phiV' k r b = ∑ c, τ c b • ((g * κ) *ᵥ phiV' k r c) := by
    rw [← Matrix.mulVec_mulVec, hY b, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  rw [e, herm_sum_l]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem dl_left {x κ : Mat k r} (hx : x ∈ GV k r) (hκ : κ ∈ GV k r) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hτ : τ.BlockTriangular id) (hY : ∀ a, x *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b))
    (g : Mat k r) (l : Fin (r + 1)) : ‖Dl k r l (x⁻¹ * g)‖₊ = cl τ l * ‖Dl k r l (κ⁻¹ * g)‖₊ := by
  rw [dl_eq, dl_eq, pm_left hx hκ τ hY, sub_tri_mul _ _ _ hτ, Matrix.det_mul,
    Matrix.det_conjTranspose, Matrix.det_of_upperTriangular (tri_sub _ τ hτ), nnnorm_mul,
    nnnorm_star, nnnorm_prod]
  rfl

theorem dl_right {y κ : Mat k r} (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hτ : τ.BlockTriangular id) (hY : ∀ a, y *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b))
    (g : Mat k r) (l : Fin (r + 1)) : ‖Dl k r l (g * y)‖₊ = cl τ l * ‖Dl k r l (g * κ)‖₊ := by
  rw [dl_eq, dl_eq, pm_right τ hY, sub_mul_tri _ _ _ hτ, Matrix.det_mul,
    Matrix.det_of_upperTriangular (tri_sub _ τ hτ), nnnorm_mul, nnnorm_prod, mul_comm]
  rfl

theorem fsE_fac (s : Fin (r + 1) → ℝ) (g1 g2 : Mat k r) (c : Fin (r + 1) → ℝ≥0)
    (h : ∀ l, ‖Dl k r l g1‖₊ = c l * ‖Dl k r l g2‖₊) :
    FsE k r s g1 = (∏ l, ((c l : ℝ≥0∞)) ^ (-s l)) * FsE k r s g2 := by
  unfold FsE
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [h l, ENNReal.coe_mul, ENNReal.mul_rpow_of_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top]

end dl

end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
end
end

