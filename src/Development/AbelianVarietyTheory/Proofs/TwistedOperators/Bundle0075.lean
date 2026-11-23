module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0490

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryHeisenbergRadicalCoordinates
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta.HeisCoord

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

def Shape (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (r b : Fin N → L) (c : L) : Prop :=
  M 0 0 = 1 ∧ (∀ j, M 0 (mid j) = r j) ∧ M 0 (Fin.last (N + 1)) = c ∧ (∀ i, M (mid i) 0 = 0) ∧
  (∀ i j, M (mid i) (mid j) = if i = j then 1 else 0) ∧ (∀ i, M (mid i) (Fin.last (N + 1)) = b i) ∧
  M (Fin.last (N + 1)) 0 = 0 ∧ (∀ j, M (Fin.last (N + 1)) (mid j) = 0) ∧
  M (Fin.last (N + 1)) (Fin.last (N + 1)) = 1

theorem form_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (cT σ M * antiJ L n * M) i j = ∑ l, σ (M l.rev i) * M l j := by
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [P.fSatake_cTJ]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem antiJ_eq {n : ℕ} (a b : Fin n) : antiJ L n a b = if a = b.rev then 1 else 0 := by
  simp only [antiJ, P.fSatake_rev_iff]

theorem shape_of_mem {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) : Shape (mat u) (rowOf u) (colOf u) (cornerOf u) := by
  have h : ∀ i j, blk N j ≤ blk N i → mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j := hu
  refine ⟨?_, fun j => rfl, rfl, fun i => ?_, fun i j => ?_, fun i => rfl, ?_, fun j => ?_, ?_⟩
  · rw [h 0 0 le_rfl, Matrix.one_apply_eq]
  · rw [h _ _ (by simp), Matrix.one_apply_ne (mid_ne_zero i)]
  · rw [h _ _ (by simp)]; simp [Matrix.one_apply, mid_injective.eq_iff]
  · rw [h _ _ (by simp), Matrix.one_apply_ne last_ne_zero]
  · rw [h _ _ (by simp), Matrix.one_apply_ne (mid_ne_last j).symm]
  · rw [h _ _ le_rfl, Matrix.one_apply_eq]

theorem sum_rev_ite {M : Type} [AddCommMonoid M] (f : Fin N → M) (j : Fin N) :
    (∑ x, if x.rev = j then f x else 0) = f j.rev := by
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro x _ hx
    rw [if_neg fun e => hx (by rw [← e, Fin.rev_rev])]
  · simp

theorem form_mid_last {M : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {r b : Fin N → L} {c : L} (h : Shape M r b c)
    (j : Fin N) : (cT σ M * antiJ L (N + 2) * M) (mid j) (Fin.last (N + 1)) = b j.rev + σ (r j) := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := h
  rw [form_apply, sum_idx]
  simp [Fin.rev_zero, Fin.rev_last, ← mid_rev, h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll, sum_rev_ite]

theorem form_last_last {M : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {r b : Fin N → L} {c : L} (h : Shape M r b c) :
    (cT σ M * antiJ L (N + 2) * M) (Fin.last (N + 1)) (Fin.last (N + 1)) = c + ∑ k, σ (b k.rev) * b k + σ c := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := h
  rw [form_apply, sum_idx]
  simp [Fin.rev_zero, Fin.rev_last, ← mid_rev, h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll, sum_rev_ite]

theorem zero_ne_mid (i : Fin N) : (0 : Fin (N + 2)) ≠ mid i := (mid_ne_zero i).symm
theorem last_ne_mid (i : Fin N) : Fin.last (N + 1) ≠ mid i := (mid_ne_last i).symm

theorem form_eq_of (hσσ : ∀ x, σ (σ x) = x) {M : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {r b : Fin N → L} {c : L}
    (h : Shape M r b c) (h1 : ∀ j, b j.rev + σ (r j) = 0) (h2 : c + ∑ k, σ (b k.rev) * b k + σ c = 0) :
    cT σ M * antiJ L (N + 2) * M = antiJ L (N + 2) := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := h
  ext i j
  rw [form_apply, sum_idx, antiJ_eq]
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [Fin.rev_zero, Fin.rev_last, ← mid_rev, h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll, sum_rev_ite,
      mid_ne_zero, mid_ne_last, zero_ne_mid, last_ne_mid, mid_injective.eq_iff]
  · by_cases e : i = j.rev
    · subst e; simp
    · rw [if_neg e, if_neg fun e' => e e'.symm]
  · exact h1 i
  · have := congrArg σ (h1 j)
    simp only [map_add (f := _), hσσ, map_zero] at this
    linear_combination this
  · exact h2

def heisMat (r b : Fin N → L) (c : L) : Matrix (Fin (N + 2)) (Fin (N + 2)) L := fun i j =>
  if i = j then 1
  else if i = 0 ∧ j = Fin.last (N + 1) then c
  else if h : i = 0 ∧ 0 < j.val ∧ j.val < N + 1 then r ⟨j.val - 1, by omega⟩
  else if h : j = Fin.last (N + 1) ∧ 0 < i.val ∧ i.val < N + 1 then b ⟨i.val - 1, by omega⟩
  else 0

theorem shape_heisMat (r b : Fin N → L) (c : L) : Shape (heisMat r b c) r b c := by
  refine ⟨by simp [heisMat], fun j => ?_, by simp [heisMat, last_ne_zero.symm], fun i => ?_, fun i j => ?_,
    fun i => ?_, by simp [heisMat, last_ne_zero], fun j => ?_, by simp [heisMat]⟩
  · have := j.2
    simp [heisMat, zero_ne_mid, mid_ne_last]
  · simp [heisMat, mid_ne_zero, last_ne_zero.symm]
  · simp [heisMat, mid_injective.eq_iff, mid_ne_zero, mid_ne_last]
  · have := i.2
    simp [heisMat, mid_ne_zero, mid_ne_last]
  · simp [heisMat, last_ne_mid, last_ne_zero]

theorem mem_radQ_of_shape {u : GU σ (N + 2)} {r b : Fin N → L} {c : L} (h : Shape (mat u) r b c) :
    u ∈ radQ σ N := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := h
  intro i j hij
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [Matrix.one_apply, h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll, mid_ne_zero, mid_ne_last, zero_ne_mid,
      last_ne_mid, mid_injective.eq_iff] at hij ⊢

theorem mul_coords {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N) :
    rowOf (u * u') = rowOf u + rowOf u' ∧ colOf (u * u') = colOf u + colOf u' ∧
      cornerOf (u * u') = cornerOf u + cornerOf u' + rowOf u ⬝ᵥ colOf u' := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := shape_of_mem hu
  obtain ⟨h00', h0m', h0l', hm0', hmm', hml', hl0', hlm', hll'⟩ := shape_of_mem hu'
  refine ⟨funext fun j => ?_, funext fun i => ?_, ?_⟩
  · simp only [rowOf, mat_mul, Matrix.mul_apply, sum_idx, Pi.add_apply]
    simp [h00, h0m, h0l, hmm', hl0', hlm', h0m']
    ring
  · simp only [colOf, mat_mul, Matrix.mul_apply, sum_idx, Pi.add_apply]
    simp [hm0, hmm, hml, hml', hll', h0l']
    ring
  · simp only [cornerOf, mat_mul, Matrix.mul_apply, sum_idx, dotProduct]
    simp [h00, h0m, h0l, hml', hll', h0l']
    ring

theorem Heisenberg₂ : Heis := by
  intro L _ _ ϖ σ q N hU
  obtain ⟨hσσ, hv, -⟩ := hU
  have hσint : ∀ x, x ∈ intL L → σ x ∈ intL L := fun x hx => by
    show Valued.v (σ x) ≤ 1
    rw [hv]; exact hx
  refine ⟨fun u hu => ?_, fun u hu u' hu' => mul_coords hu hu', fun r c hc => ?_⟩
  · have hs := shape_of_mem hu
    have hf : cT σ (mat u) * antiJ L (N + 2) * mat u = antiJ L (N + 2) := u.2
    have h1 : ∀ j, colOf u j.rev + σ (rowOf u j) = 0 := fun j => by
      have := congrFun (congrFun hf (mid j)) (Fin.last (N + 1))
      rwa [form_mid_last hs, antiJ_eq, if_neg (by rw [Fin.rev_last]; exact mid_ne_zero j)] at this
    have h2 : cornerOf u + ∑ k, σ (colOf u k.rev) * colOf u k + σ (cornerOf u) = 0 := by
      have := congrFun (congrFun hf (Fin.last (N + 1))) (Fin.last (N + 1))
      rwa [form_last_last hs, antiJ_eq, if_neg (by rw [Fin.rev_last]; exact last_ne_zero)] at this
    have hr : ∀ j, rowOf u j = -σ (colOf u j.rev) := fun j => by
      have := congrArg σ (h1 j)
      simp only [map_add (f := _), hσσ, map_zero] at this
      linear_combination this
    refine ⟨hr, ?_, ?_⟩
    · simp only [dotProduct, hr, neg_mul, Finset.sum_neg_distrib]
      linear_combination h2
    · rw [mem_KU_iff hv]
      constructor
      · intro h
        exact ⟨fun j => h _ _, h _ _⟩
      · rintro ⟨hr', hc'⟩ i j
        obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := hs
        have hb : ∀ i, colOf u i ∈ intL L := fun i => by
          have e := hr i.rev
          rw [Fin.rev_rev] at e
          have h' : colOf u i = -σ (rowOf u i.rev) := by rw [e, map_neg, hσσ, neg_neg]
          rw [h']
          exact neg_mem (hσint _ (hr' _))
        rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
          simp only [h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll] <;>
          first | exact one_mem _ | exact zero_mem _ | exact hr' _ | exact hc' | exact hb _ |
            (split_ifs <;> first | exact one_mem _ | exact zero_mem _)
  · let b : Fin N → L := fun i => -σ (r i.rev)
    have h1 : ∀ j, b j.rev + σ (r j) = 0 := fun j => by simp [b]
    have h2 : c + ∑ k, σ (b k.rev) * b k + σ c = 0 := by
      simp only [b, Fin.rev_rev, map_neg, hσσ, neg_mul_neg]
      linear_combination hc
    obtain ⟨g, hg⟩ := exists_mat (σ := σ) (heisMat r b c) (form_eq_of hσσ (shape_heisMat r b c) h1 h2)
    have hs : Shape (mat g) r b c := hg ▸ shape_heisMat r b c
    exact ⟨g, mem_radQ_of_shape hs, funext hs.2.1, hs.2.2.1⟩

end GlobalTheory.InertZeta.HeisCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIwasawaCellsDisjoint
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem blk_eq_zero_iff {l : Fin (N + 2)} : blk N l = 0 ↔ l = 0 := by
  rcases idx_cases l with rfl | ⟨j, rfl⟩ | rfl
  · simp
  · simp [mid_ne_zero]
  · simp [last_ne_zero]

theorem blk_eq_two_iff {l : Fin (N + 2)} : blk N l = 2 ↔ l = Fin.last (N + 1) := by
  rcases idx_cases l with rfl | ⟨j, rfl⟩ | rfl
  · simp [(last_ne_zero (N := N)).symm]
  · simp [mid_ne_last]
  · simp

theorem levi_mul_apply_zero {x : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L)
    (j : Fin (N + 2)) : (mat x * M) 0 j = mat x 0 0 * M 0 j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single 0]
  · intro l _ hl
    rw [hx 0 l (by rw [blk_zero]; exact fun h => hl (blk_eq_zero_iff.1 h.symm)), zero_mul]
  · simp

theorem levi_mul_apply_last {x : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L)
    (j : Fin (N + 2)) : (mat x * M) (Fin.last (N + 1)) j = mat x (Fin.last (N + 1)) (Fin.last (N + 1)) * M (Fin.last (N + 1)) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last (N + 1))]
  · intro l _ hl
    rw [hx _ l (by rw [blk_last]; exact fun h => hl (blk_eq_two_iff.1 h.symm)), zero_mul]
  · simp

theorem levi_mul_apply_mid {x : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L)
    (i j : Fin (N + 2)) (k : Fin N) (hi : i = mid k) :
    (mat x * M) i j = ∑ l, mat x i (mid l) * M (mid l) j := by
  subst hi
  rw [Matrix.mul_apply, sum_idx (fun l => mat x (mid k) l * M l j), hx (mid k) 0 (by simp), hx (mid k) _ (by simp)]
  simp

end

theorem cosetInj : CosetInj := by
  intro L _ _ ϖ σ q N hU a a' g₀ g₀' m m' hm hm' u hu u' hu' hK
  have hσ : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have hϖ0 : ϖ ≠ 0 := fun h => by rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hvz : ∀ k : ℤ, Valued.v (ϖ ^ k) = WithZero.exp (-k) := fun k => by
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; simp
  set n := m⁻¹ * m' with hn_def
  have hnL : n ∈ leviU σ (blk N) := mul_mem (inv_mem hm.1) hm'.1
  have hconj : n⁻¹ * u⁻¹ * n⁻¹⁻¹ ∈ radQ σ N :=
    (leviRad L σ (N + 2) (blk N) hσ n⁻¹ (inv_mem hnL) u⁻¹ (inv_mem hu)).1
  have he : (m * u)⁻¹ * (m' * u') = n * ((n⁻¹ * u⁻¹ * n⁻¹⁻¹) * u') := by
    rw [hn_def]; group
  have hnK : n ∈ KU σ (N + 2) :=
    (leviRad L σ (N + 2) (blk N) hσ n hnL _ (mul_mem hconj hu')).2 (he ▸ hK)
  have hint : ∀ i j, mat n i j ∈ intL L := (mem_KU_iff hσ n).1 hnK
  have hmn : mat m * mat n = mat m' := by rw [← mat_mul, hn_def, mul_inv_cancel_left]
  have h0 : ϖ ^ a * mat n 0 0 = ϖ ^ a' := by
    rw [← hm.2.1, ← hm'.2.1, ← hmn, levi_mul_apply_zero hm.1]
  have hl : ϖ ^ (-a) * mat n (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a') := by
    rw [← hm.2.2.1, ← hm'.2.2.1, ← hmn, levi_mul_apply_last hm.1]
  have hv0 := hint 0 0
  have hvl := hint (Fin.last (N + 1)) (Fin.last (N + 1))
  have e0 : mat n 0 0 = ϖ ^ (a' - a) := by
    rw [zpow_sub₀ hϖ0, ← h0]; field_simp
  have el : mat n (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (a - a') := by
    rw [show a - a' = -a' - -a by ring, zpow_sub₀ hϖ0, ← hl]; field_simp
  change Valued.v (mat n 0 0) ≤ 1 at hv0
  change Valued.v (mat n (Fin.last (N + 1)) (Fin.last (N + 1))) ≤ 1 at hvl
  rw [e0, hvz, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv0
  rw [el, hvz, ← WithZero.exp_zero, WithZero.exp_le_exp] at hvl
  refine ⟨by omega, ?_⟩
  rw [mem_KU_iff hσ]
  have hmid : mat g₀ * Matrix.of (fun i j => mat n (mid i) (mid j)) = mat g₀' := by
    ext i j
    rw [← hm'.2.2.2, ← hmn, levi_mul_apply_mid hm.1 _ _ _ i rfl, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [hm.2.2.2]; rfl
  intro i j
  rw [mat_mul, ← hmid, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
  exact hint _ _

end GlobalTheory.InertZeta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIwasawaCosetSurjOfLeviElementExists
section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem rev_zero_eq_last {N : ℕ} : (0 : Fin (N + 2)).rev = Fin.last (N + 1) := by ext; simp [Fin.val_rev]

theorem rev_last_eq_zero {N : ℕ} : (Fin.last (N + 1)).rev = (0 : Fin (N + 2)) := by ext; simp [Fin.val_rev]

theorem blk_rev_of_eq {N : ℕ} (a b : Fin (N + 2)) (h : blk N a = blk N b) : blk N a.rev = blk N b.rev := by
  rcases idx_cases a with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases b with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [rev_zero_eq_last, rev_last_eq_zero, ← mid_rev] at h ⊢

theorem lt_of_blk_lt {N : ℕ} {a b : Fin (N + 2)} (h : blk N a < blk N b) : a < b := by
  rcases idx_cases a with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases b with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [Fin.lt_def] at h ⊢

theorem cosetSurj_of_leviExists : LeviExists → CosetSurj := by
  intro _ L _ _ ϖ σ q N hU g
  have hσσ : ∀ x, σ (σ x) = x := hU.1
  have hσv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  have hσϖ : σ ϖ = ϖ := hU.2.2.1
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  obtain ⟨b, k, hb, hk, rfl⟩ := P.fIwasawa_iwasawa σ hσσ hσv g
  have hbT : (mat b).BlockTriangular (blk N) := fun i j h => hb i j (lt_of_blk_lt h)
  obtain ⟨m', hm'L, hm'e, hu'⟩ := leviPart L σ (N + 2) (blk N) blk_rev_of_eq b hbT
  set M₀ : Matrix (Fin N) (Fin N) L := Matrix.of fun i j => mat m' (mid i) (mid j) with hM₀
  have hM₀U : cT σ M₀ * antiJ L N * M₀ = antiJ L N := by
    have h1 : cT σ (mat m') * antiJ L (N + 2) * mat m' = antiJ L (N + 2) := m'.2
    ext i j
    have h2 := congrFun (congrFun h1 (mid i)) (mid j)
    rw [Matrix.mul_apply, sum_idx] at h2
    have e0 : mat m' 0 (mid j) = 0 := hm'L _ _ (by simp)
    have eL : mat m' (Fin.last (N + 1)) (mid j) = 0 := hm'L _ _ (by simp)
    rw [e0, eL, mul_zero, mul_zero, zero_add, add_zero] at h2
    have hJ : antiJ L (N + 2) (mid i) (mid j) = antiJ L N i j := by
      simp only [antiJ]
      exact if_congr (by simp only [val_mid]; omega) rfl rfl
    rw [hJ] at h2
    rw [← h2, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [P.fSatake_cTJ, P.fSatake_cTJ, ← mid_rev]
    rfl
  obtain ⟨g₀, hg₀⟩ := exists_mat M₀ hM₀U
  obtain ⟨⟨k₀, hk₀⟩, hout⟩ := QuotientGroup.mk_out_eq_mul (KU σ N) g₀
  have hxL : σ (mat m' 0 0) * mat m' (Fin.last (N + 1)) (Fin.last (N + 1)) = 1 := by
    rw [hm'e 0 0 rfl, hm'e _ _ rfl]
    have := P.fSatake_unit_diag hb 0
    rwa [rev_zero_eq_last] at this
  have hx0 : mat m' 0 0 ≠ 0 := by
    intro h; rw [h, map_zero, zero_mul] at hxL; exact zero_ne_one hxL
  have hvx0 : Valued.v (mat m' 0 0) ≠ 0 := by simpa using hx0
  have hvx : Valued.v (mat m' 0 0) = WithZero.exp (-(-(Valued.v (mat m' 0 0)).log)) := by
    rw [neg_neg, WithZero.exp_log hvx0]
  refine ⟨-(Valued.v (mat m' 0 0)).log, (g₀ : GU σ N ⧸ KU σ N), fun m hm => ?_⟩
  obtain ⟨hmL, hm0, hmLL, hmM⟩ := hm
  generalize -(Valued.v (mat m' 0 0)).log = a at hvx hm0 hmLL
  have hmiL : m⁻¹ ∈ leviU σ (blk N) := inv_mem hmL
  have hcL : m⁻¹ * m' ∈ leviU σ (blk N) := mul_mem hmiL hm'L
  have hcK : m⁻¹ * m' ∈ KU σ (N + 2) := by
    rw [mem_KU_iff hσv]
    intro i j
    by_cases hij : blk N i = blk N j
    swap
    · rw [hcL i j hij]; exact zero_mem _
    rw [mat_mul, Matrix.mul_apply, sum_idx]
    rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
      simp at hij
    · rw [Finset.sum_eq_zero (fun l _ => by rw [hmiL 0 (mid l) (by simp), zero_mul]),
        hmiL 0 (Fin.last _) (by simp), zero_mul, add_zero, add_zero, mat_inv_apply, rev_zero_eq_last, hmLL,
        map_zpow₀, hσϖ]
      rw [intL, Valuation.mem_integer_iff]
      rw [map_mul, map_zpow₀, hϖ, hvx, ← WithZero.exp_zsmul, ← WithZero.exp_add,
        show (-a) • (-1 : ℤ) + -a = 0 by rw [smul_eq_mul]; ring, WithZero.exp_zero]
    · rw [hmiL (mid i) 0 (by simp), zero_mul, zero_add, hmiL (mid i) (Fin.last _) (by simp), zero_mul, add_zero]
      have e : ∑ l, mat m⁻¹ (mid i) (mid l) * mat m' (mid l) (mid j) = mat ((g₀ * k₀)⁻¹ * g₀) i j := by
        rw [mat_mul, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [mat_inv_apply, mat_inv_apply, ← mid_rev, ← mid_rev, hmM, hout, hg₀]
        rfl
      rw [e, show (g₀ * k₀)⁻¹ * g₀ = k₀⁻¹ by group]
      exact P.fSatake_K_int (inv_mem hk₀) i j
    · rw [Finset.sum_eq_zero (fun l _ => by rw [hmiL (Fin.last _) (mid l) (by simp), zero_mul]),
        hmiL (Fin.last _) 0 (by simp), zero_mul, zero_add, zero_add, mat_inv_apply, rev_last_eq_zero, hm0,
        map_zpow₀, hσϖ, eq_inv_of_mul_eq_one_right hxL, intL, Valuation.mem_integer_iff, map_mul, map_inv₀, hσv,
        map_zpow₀, hϖ, hvx, ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add,
        show a • (-1 : ℤ) + -(-a) = 0 by rw [smul_eq_mul]; ring, WithZero.exp_zero]
  obtain ⟨hr, -⟩ := leviRad L σ (N + 2) (blk N) hσv (m⁻¹ * m') hcL (m'⁻¹ * b) hu'
  exact ⟨(m⁻¹ * m') * (m'⁻¹ * b) * (m⁻¹ * m')⁻¹, hr, (m⁻¹ * m') * k, mul_mem hcK hk, by group⟩

end GlobalTheory.InertZeta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryRankLeOneIntegralPoints
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem smallRank : SmallRank := by
  intro L _ _ ϖ σ q n hU hn g

  set A : Matrix (Fin n) (Fin n) L := ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAdef
  set B : Matrix (Fin n) (Fin n) L := (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
    with hBdef
  have hAB : A * B = 1 := (g : GL (Fin n) L).mul_inv
  have hBA : B * A = 1 := (g : GL (Fin n) L).inv_mul

  have hherm : (A.map σ)ᵀ * antiJ L n * A = antiJ L n := g.2

  have key : ∀ i j, Valued.v (A i j) = 1 ∧ Valued.v (B i j) = 1 := by
    intro i j
    obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · exact i.elim0
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      have h1 : σ (A 0 0) * A 0 0 = 1 := by
        simpa [Matrix.mul_apply, antiJ] using congrFun (congrFun hherm 0) 0
      have h2 : B 0 0 * A 0 0 = 1 := by
        simpa [Matrix.mul_apply] using congrFun (congrFun hBA 0) 0
      have hsq : Valued.v (A 0 0) * Valued.v (A 0 0) = 1 := by
        have := congrArg Valued.v h1
        rwa [map_mul, map_one, hU.2.1] at this
      have hle : Valued.v (A 0 0) ≤ 1 := by
        by_contra hlt
        have hgt : 1 < Valued.v (A 0 0) := not_le.1 hlt
        have : Valued.v (A 0 0) * 1 ≤ Valued.v (A 0 0) * Valued.v (A 0 0) := by gcongr
        rw [mul_one, hsq] at this
        exact hlt this
      have hA1 : Valued.v (A 0 0) = 1 := by
        refine le_antisymm hle ?_
        have : Valued.v (A 0 0) * Valued.v (A 0 0) ≤ Valued.v (A 0 0) * 1 := by gcongr
        rwa [mul_one, hsq] at this
      refine ⟨hA1, ?_⟩
      have := congrArg Valued.v h2
      rwa [map_mul, map_one, hA1, mul_one] at this
  have hint : ∀ x : L, Valued.v x = 1 → x ∈ intL L := fun x hx => by
    unfold intL
    exact (Valuation.mem_integer_iff _ _).2 hx.le

  let A' : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨A i j, hint _ (key i j).1⟩
  let B' : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨B i j, hint _ (key i j).2⟩
  have hinj : Function.Injective
      ((intL L).subtype.mapMatrix : Matrix (Fin n) (Fin n) (intL L) → Matrix (Fin n) (Fin n) L) :=
    fun X Y h => by
      ext i j
      exact congrFun (congrFun h i) j
  have eA : (intL L).subtype.mapMatrix A' = A := rfl
  have eB : (intL L).subtype.mapMatrix B' = B := rfl
  unfold KU
  rw [Subgroup.mem_subgroupOf]
  unfold intPts
  rw [Subgroup.mem_inf, MonoidHom.mem_range]
  refine ⟨g.2, ⟨A', B', hinj ?_, hinj ?_⟩, ?_⟩
  · rw [map_mul, eA, eB, map_one, hAB]
  · rw [map_mul, eA, eB, map_one, hBA]
  · unfold bc
    exact Units.ext eA

end GlobalTheory.InertZeta

end
end

