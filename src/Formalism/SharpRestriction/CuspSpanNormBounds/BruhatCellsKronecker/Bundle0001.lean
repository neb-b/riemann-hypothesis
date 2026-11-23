module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellInv
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.MainNotions.S Matrix

section

variable {K : Type} [Field K] {n : ℕ}

theorem cinv_det_up {U : Matrix (Fin n) (Fin n) K} (hU : IsUpUni U) : U.det = 1 := by
  have hT : U.BlockTriangular id := fun i j hij => (hU i j).1 hij
  rw [Matrix.det_of_upperTriangular hT]
  exact Finset.prod_eq_one (fun i _ => (hU i i).2 rfl)

theorem cinv_inv_up {U : Matrix (Fin n) (Fin n) K} (hU : IsUpUni U) : IsUpUni U⁻¹ := by
  have hdet : IsUnit U.det := by rw [cinv_det_up hU]; exact isUnit_one
  have hT : U.BlockTriangular id := fun i j hij => (hU i j).1 hij
  haveI : Invertible U := Matrix.invertibleOfIsUnitDet U hdet
  have hI : (U⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hT
  intro i j
  refine ⟨fun h => hI (show id j < id i from h), ?_⟩
  rintro rfl
  have h1 : (U⁻¹ * U) i i = 1 := by rw [Matrix.nonsing_inv_mul _ hdet]; simp
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · rwa [(hU i i).2 rfl, mul_one] at h1
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hI (show id k < id i from h), zero_mul]
    · rw [(hU k i).1 h, mul_zero]
  · simp

theorem cinv_mul_left {U A : Matrix (Fin n) (Fin n) K} (hU : IsUpUni U) (hA : StrictUp A) :
    StrictUp (U * A) ∧ ∀ (a : Fin n) (h : a.val + 1 < n), (U * A) a ⟨a.val + 1, h⟩ = A a ⟨a.val + 1, h⟩ := by
  constructor
  · intro a b hba
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_or_ge k a with h | h
    · rw [(hU a k).1 h, zero_mul]
    · rw [hA k b (le_trans hba h), mul_zero]
  · intro a h
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(hU a a).2 rfl, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h1 | h1
      · rw [(hU a k).1 h1, zero_mul]
      · rw [hA k _ (Fin.le_def.2 (Nat.succ_le_of_lt (Fin.lt_def.1 h1))), mul_zero]
    · simp

theorem cinv_mul_right {U A : Matrix (Fin n) (Fin n) K} (hU : IsUpUni U) (hA : StrictUp A) :
    StrictUp (A * U) ∧ ∀ (a : Fin n) (h : a.val + 1 < n), (A * U) a ⟨a.val + 1, h⟩ = A a ⟨a.val + 1, h⟩ := by
  constructor
  · intro a b hba
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases le_or_gt k a with h | h
    · rw [hA a k h, zero_mul]
    · rw [(hU k b).1 (lt_of_le_of_lt hba h), mul_zero]
  · intro a h
    rw [Matrix.mul_apply, Finset.sum_eq_single (⟨a.val + 1, h⟩ : Fin n)]
    · rw [(hU _ _).2 rfl, mul_one]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h1 | h1
      · rw [hA a k (Fin.le_def.2 (Nat.le_of_lt_succ (Fin.lt_def.1 h1))), zero_mul]
      · rw [(hU k _).1 h1, mul_zero]
    · simp

theorem cinv_supSum_congr {A B : Matrix (Fin n) (Fin n) K}
    (h : ∀ (a : Fin n) (h : a.val + 1 < n), B a ⟨a.val + 1, h⟩ = A a ⟨a.val + 1, h⟩) : supSum B = supSum A := by
  unfold supSum
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs with h1
  · exact h a h1
  · rfl

theorem cinv_conj {U A : Matrix (Fin n) (Fin n) K} (hU : IsUpUni U) (hA : StrictUp A) :
    StrictUp (U⁻¹ * A * U) ∧ supSum (U⁻¹ * A * U) = supSum A := by
  have b1 := cinv_mul_left (cinv_inv_up hU) hA
  have b2 := cinv_mul_right hU b1.1
  exact ⟨b2.1, cinv_supSum_congr (fun a h => (b2.2 a h).trans (b1.2 a h))⟩

end

theorem cell_inv : RelevanceUnipotentInvariant := by
  intro K _ _ n L Z U hL hU hrel A A' hA hA' hAA
  have hV : IsUpUni Lᴴ := by
    intro i j
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [Matrix.conjTranspose_apply, (hL j i).1 h, star_zero]
    · rw [Matrix.conjTranspose_apply, (hL j i).2 h.symm, star_one]
  have dU : IsUnit U.det := by rw [cinv_det_up hU]; exact isUnit_one
  have dL : IsUnit L.det := by
    have h : L.det = star (Lᴴ).det := by rw [Matrix.det_conjTranspose, star_star]
    rw [h, cinv_det_up hV, star_one]
    exact isUnit_one
  have b := cinv_conj hV hA
  have c := cinv_conj hU hA'
  have e1 : ((Lᴴ)⁻¹ * A * Lᴴ)ᴴ = L * Aᴴ * L⁻¹ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have e2 : L * Aᴴ * L⁻¹ * (L * Z * U) = L * (Aᴴ * Z) * U := by
    calc L * Aᴴ * L⁻¹ * (L * Z * U) = L * Aᴴ * (L⁻¹ * L) * Z * U := by simp only [Matrix.mul_assoc]
      _ = L * (Aᴴ * Z) * U := by rw [Matrix.nonsing_inv_mul _ dL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e3 : L * Z * U * (U⁻¹ * A' * U) = L * (Z * A') * U := by
    calc L * Z * U * (U⁻¹ * A' * U) = L * Z * (U * U⁻¹) * A' * U := by simp only [Matrix.mul_assoc]
      _ = L * (Z * A') * U := by rw [Matrix.mul_nonsing_inv _ dU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have key := hrel ((Lᴴ)⁻¹ * A * Lᴴ) (U⁻¹ * A' * U) b.1 c.1 (by
    rw [e1, e2, e3, ← Matrix.add_mul, ← Matrix.mul_add, hAA, Matrix.mul_zero, Matrix.zero_mul])
  rwa [b.2, c.2] at key

theorem cell_sign : ColumnScalingBruhatShape := by
  intro K _ n ε L U σ t hε hU
  refine ⟨diagonal (fun a => (ε a)⁻¹) * U * diagonal ε, ?_, ?_⟩
  · intro i j
    have e : (diagonal (fun a => (ε a)⁻¹) * U * diagonal ε) i j = (ε i)⁻¹ * U i j * ε j := by
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    refine ⟨fun h => by rw [e, (hU i j).1 h]; ring, fun h => ?_⟩
    subst h
    rw [e, (hU i i).2 rfl, mul_one, inv_mul_cancel₀ (hε i)]
  · have hm : mono σ (fun b => ε b * t b) = mono σ t * diagonal ε := by
      ext a b
      rw [Matrix.mul_diagonal]
      unfold mono
      split_ifs <;> ring
    have hd : diagonal ε * diagonal (fun a => (ε a)⁻¹) = (1 : Matrix (Fin n) (Fin n) K) := by
      rw [Matrix.diagonal_mul_diagonal]
      have h1 : (fun i => ε i * (ε i)⁻¹) = fun _ => (1 : K) := funext fun i => mul_inv_cancel₀ (hε i)
      rw [h1, Matrix.diagonal_one]
    have hl : (fun a b => ε b * (L * mono σ t * U) a b) = L * mono σ t * U * diagonal ε := by
      funext a b
      rw [Matrix.mul_diagonal, mul_comm]
    refine hl.trans ?_
    rw [hm]
    calc L * mono σ t * U * diagonal ε = L * mono σ t * 1 * U * diagonal ε := by rw [Matrix.mul_one]
      _ = L * (mono σ t * diagonal ε) * (diagonal (fun a => (ε a)⁻¹) * U * diagonal ε) := by
        rw [← hd]; simp only [Matrix.mul_assoc]

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellMono
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.MainNotions.S Matrix

section

variable {K : Type} [Field K] {n : ℕ}

def cmonoE (p q : Fin n) (y : K) : Matrix (Fin n) (Fin n) K := fun a b => if a = p ∧ b = q then y else 0

theorem cmono_strict (p q : Fin n) (y : K) (h : p < q) : StrictUp (cmonoE p q y) := by
  intro a b hab
  unfold cmonoE
  rw [if_neg]
  rintro ⟨rfl, rfl⟩
  exact absurd h (not_lt.2 hab)

theorem cmono_supSum_succ (p q : Fin n) (y : K) (h : q.val = p.val + 1) : supSum (cmonoE p q y) = y := by
  unfold supSum
  rw [Finset.sum_eq_single p]
  · have hp : p.val + 1 < n := h ▸ q.isLt
    rw [dite_eq_left hp]
    unfold cmonoE
    rw [if_pos ⟨rfl, Fin.ext h.symm⟩]
  · intro a _ hne
    split_ifs with h1
    · unfold cmonoE
      rw [if_neg (fun hh => hne hh.1)]
    · rfl
  · intro hh
    exact absurd (Finset.mem_univ p) hh

theorem cmono_supSum_ne (p q : Fin n) (y : K) (h : q.val ≠ p.val + 1) : supSum (cmonoE p q y) = 0 := by
  unfold supSum
  refine Finset.sum_eq_zero (fun a _ => ?_)
  split_ifs with h1
  · unfold cmonoE
    rw [if_neg]
    rintro ⟨rfl, h2⟩
    exact h (by rw [← h2])
  · rfl

theorem cmono_left [StarRing K] (σ : Fin n → Fin n) (t : Fin n → K) (hσ : Function.Injective σ) (b : Fin n) (q : Fin n)
    (y : K) (i j : Fin n) :
    ((cmonoE (σ b) q y)ᴴ * mono σ t) i j = if i = q ∧ j = b then star y * t b else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ j)]
  · simp only [Matrix.conjTranspose_apply, cmonoE, mono, if_true]
    by_cases h1 : i = q ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h1
      simp
    · rw [if_neg h1, if_neg, star_zero, zero_mul]
      rintro ⟨h2, h3⟩
      exact h1 ⟨h3, hσ h2⟩
  · intro k _ hk
    simp only [mono]
    rw [if_neg hk, mul_zero]
  · intro hh
    exact absurd (Finset.mem_univ _) hh

theorem cmono_right (σ : Fin n → Fin n) (t : Fin n → K) (c b : Fin n) (x : K) (i j : Fin n) :
    (mono σ t * cmonoE c b x) i j = if i = σ c ∧ j = b then t c * x else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single c]
  · simp only [cmonoE, mono, true_and]
    by_cases h1 : i = σ c
    · by_cases h2 : j = b
      · simp [h1, h2]
      · simp [h1, h2]
    · simp [h1]
  · intro k _ hk
    simp only [cmonoE]
    rw [if_neg (fun hh => hk hh.1), mul_zero]
  · intro hh
    exact absurd (Finset.mem_univ _) hh

end

theorem cell_mono : RelevantMonomialConsecutive := by
  intro K _ _ n σ t hσ ht hrel c b hcb hv
  have htb : t b ≠ 0 := ht b
  have htc : t c ≠ 0 := ht c
  have hlt : σ b < σ c := Fin.lt_def.2 (by omega)

  set y : K := star (-(t c / t b)) with hy
  have hsy : star y * t b + t c * 1 = 0 := by
    rw [hy, star_star]
    field_simp
    ring
  have hR : (cmonoE (σ b) (σ c) y)ᴴ * mono σ t + mono σ t * cmonoE c b 1 = 0 := by
    ext i j
    rw [Matrix.add_apply, cmono_left σ t hσ.1, cmono_right, Matrix.zero_apply]
    by_cases h : i = σ c ∧ j = b
    · rw [if_pos h, if_pos h, hsy]
    · rw [if_neg h, if_neg h, add_zero]
  have h := hrel _ _ (cmono_strict (σ b) (σ c) y hlt) (cmono_strict c b 1 hcb) hR
  rw [cmono_supSum_succ (σ b) (σ c) y hv] at h
  have hy0 : y ≠ 0 := by
    rw [hy]
    intro h0
    have h1 : -(t c / t b) = 0 := by simpa using h0
    exact (div_ne_zero htc htb) (neg_eq_zero.1 h1)
  by_cases hb : b.val = c.val + 1
  · refine ⟨hb, ?_⟩
    rw [cmono_supSum_succ c b 1 hb, star_one] at h
    rw [h, star_one, one_mul, mul_one] at hsy
    exact eq_neg_of_add_eq_zero_left hsy
  · rw [cmono_supSum_ne c b 1 hb, star_zero] at h
    exact absurd h hy0

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellPt
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.MainNotions.S

theorem cpt_nat {K : Type} [Field K] : ∀ (n : ℕ) (σ : ℕ → ℕ) (τ : ℕ → K),
    (∀ i, i < n → σ i < n) → (∀ i, i < n → ∀ j, j < n → σ i = σ j → i = j) → (∀ v, v < n → ∃ i, i < n ∧ σ i = v) →
    (∀ i, i < n → τ i ≠ 0) →
    (∀ c b, c < b → b < n → σ c = σ b + 1 → b = c + 1 ∧ τ b = τ c) →
    ∃ bs : List (K × ℕ), (∀ x ∈ bs, x.1 ≠ 0 ∧ 1 ≤ x.2) ∧ (bs.map Prod.snd).sum = n ∧
      ∀ a, a < n → ∀ b, b < n → ptEntry bs a b = if a = σ b then τ b else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ τ hmap hinj hsurj hτ hP
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      exact ⟨[], by simp, by simp, fun a ha => absurd ha (Nat.not_lt_zero a)⟩
    · obtain ⟨s, hs⟩ : ∃ s, s = σ 0 + 1 := ⟨_, rfl⟩
      have hsn : s ≤ n := by have := hmap 0 hpos; omega
      have hs1 : 1 ≤ s := by omega

      have c1 : ∀ i, i < s → σ i = s - 1 - i ∧ τ i = τ 0 := by
        intro i
        induction i using Nat.strong_induction_on with
        | _ i ihi =>
          intro hi
          rcases Nat.eq_zero_or_pos i with hi0 | hipos
          · subst hi0
            exact ⟨by omega, rfl⟩
          · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
            obtain ⟨e1, e2⟩ := ihi i' (by omega) (by omega)
            obtain ⟨b, hbn, hb⟩ := hsurj (s - 1 - (i' + 1)) (by omega)
            have hbi : i' + 1 ≤ b := by
              by_contra hlt
              have := (ihi b (by omega) (by omega)).1
              omega
            obtain ⟨f1, f2⟩ := hP i' b (by omega) hbn (by omega)
            subst f1
            exact ⟨hb, f2.trans e2⟩

      have c2 : ∀ i, s ≤ i → i < n → s ≤ σ i := by
        intro i hi hin
        by_contra hlt
        have hj : s - 1 - σ i < s := by omega
        have e := (c1 (s - 1 - σ i) hj).1
        have := hinj i hin (s - 1 - σ i) (by omega) (by omega)
        omega
      obtain ⟨bs, hb1, hb2, hb3⟩ := ih (n - s) (by omega) (fun i => σ (i + s) - s) (fun i => τ (i + s))
        (fun i hi => by
          have h1 := hmap (i + s) (by omega)
          have h2 := c2 (i + s) (by omega) (by omega)
          show σ (i + s) - s < n - s
          omega)
        (fun i hi j hj hij => by
          have h1 := c2 (i + s) (by omega) (by omega)
          have h2 := c2 (j + s) (by omega) (by omega)
          have h3 : σ (i + s) - s = σ (j + s) - s := hij
          have := hinj (i + s) (by omega) (j + s) (by omega) (by omega)
          omega)
        (fun v hv => by
          obtain ⟨i, hin, hi⟩ := hsurj (v + s) (by omega)
          have his : s ≤ i := by
            by_contra hlt
            have := (c1 i (by omega)).1
            omega
          refine ⟨i - s, by omega, ?_⟩
          show σ (i - s + s) - s = v
          rw [Nat.sub_add_cancel his, hi]
          omega)
        (fun i hi => hτ (i + s) (by omega))
        (fun c b hcb hbn hv => by
          have h1 := c2 (c + s) (by omega) (by omega)
          have h2 := c2 (b + s) (by omega) (by omega)
          have h3 : σ (c + s) - s = σ (b + s) - s + 1 := hv
          obtain ⟨f1, f2⟩ := hP (c + s) (b + s) (by omega) (by omega) (by omega)
          exact ⟨by omega, f2⟩)
      refine ⟨(τ 0, s) :: bs, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨hτ 0 hpos, hs1⟩
        · exact hb1 x hx
      · simp only [List.map_cons, List.sum_cons, hb2]
        omega
      · intro a ha b hb
        simp only [ptEntry]
        by_cases h1 : a < s ∧ b < s
        · rw [if_pos h1]
          obtain ⟨e1, e2⟩ := c1 b h1.2
          by_cases h2 : a + b + 1 = s
          · rw [if_pos h2, if_pos (by omega), e2]
          · rw [if_neg h2, if_neg (by omega)]
        · rw [if_neg h1]
          by_cases h2 : s ≤ a ∧ s ≤ b
          · rw [if_pos h2, hb3 (a - s) (by omega) (b - s) (by omega)]
            have e0 : b - s + s = b := Nat.sub_add_cancel h2.2
            have h3 := c2 b h2.2 hb
            simp only [e0]
            by_cases h4 : a = σ b
            · rw [if_pos h4, if_pos (by omega)]
            · rw [if_neg h4, if_neg (by omega)]
          · rw [if_neg h2]
            rcases Nat.lt_or_ge b s with hbs | hbs
            · have := (c1 b hbs).1
              rw [if_neg (by omega)]
            · have := c2 b hbs hb
              rw [if_neg (by omega)]

theorem cell_point : MonomialMatrixIsPoint := by
  intro K _ n σ τ hσ hτ hP
  obtain ⟨bs, h1, h2, h3⟩ := cpt_nat n (fun i => if h : i < n then (σ ⟨i, h⟩).val else 0)
    (fun i => if h : i < n then τ ⟨i, h⟩ else 0)
    (fun i hi => by simp only [dif_pos hi]; exact (σ ⟨i, hi⟩).isLt)
    (fun i hi j hj hij => by
      simp only [dif_pos hi, dif_pos hj] at hij
      have := hσ.1 (Fin.ext hij)
      exact congrArg Fin.val this)
    (fun v hv => by
      obtain ⟨i, hi⟩ := hσ.2 ⟨v, hv⟩
      refine ⟨i.val, i.isLt, ?_⟩
      simp only [dif_pos i.isLt, Fin.eta, hi])
    (fun i hi => by simp only [dif_pos hi]; exact hτ _)
    (fun c b hcb hbn hv => by
      have hcn : c < n := lt_trans hcb hbn
      simp only [dif_pos hcn, dif_pos hbn] at hv ⊢
      exact hP ⟨c, hcn⟩ ⟨b, hbn⟩ hcb hv)
  refine ⟨⟨bs, h1, h2⟩, ?_⟩
  ext a b
  show ptEntry bs a.val b.val = mono σ τ a b
  rw [h3 a.val a.isLt b.val b.isLt]
  simp only [dif_pos b.isLt, Fin.eta, mono, Fin.ext_iff]

end Formalism.MainNotions.BridgeLemma

end
end

