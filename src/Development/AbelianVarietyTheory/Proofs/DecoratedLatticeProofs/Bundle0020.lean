module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeSubsetSum
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.SatakeSubsetSum

open Finset

theorem two_mul_card_lt_pairs {N : ℕ} (S : Finset (Fin N)) :
    2 * ((S ×ˢ S).filter fun p : Fin N × Fin N => p.1 < p.2).card + S.card = S.card * S.card := by
  have hsw : ((S ×ˢ S).filter fun p : Fin N × Fin N => p.1 < p.2).card
      = ((S ×ˢ S).filter fun p : Fin N × Fin N => p.2 < p.1).card := by
    apply Finset.card_bij (fun p _ => p.swap)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p _ r _ h
      exact Prod.swap_injective h
    · intro r hr
      refine ⟨r.swap, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_product, Prod.fst_swap, Prod.snd_swap] at hr ⊢
      exact ⟨⟨hr.1.2, hr.1.1⟩, hr.2⟩
  have hoff : S.offDiag = ((S ×ˢ S).filter fun p : Fin N × Fin N => p.1 < p.2) ∪
      ((S ×ˢ S).filter fun p : Fin N × Fin N => p.2 < p.1) := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases lt_or_gt_of_ne h3 with h | h
      · exact Or.inl ⟨⟨h1, h2⟩, h⟩
      · exact Or.inr ⟨⟨h1, h2⟩, h⟩
    · rintro (⟨⟨h1, h2⟩, h⟩ | ⟨⟨h1, h2⟩, h⟩)
      · exact ⟨h1, h2, ne_of_lt h⟩
      · exact ⟨h1, h2, ne_of_gt h⟩
  have hdisj : Disjoint ((S ×ˢ S).filter fun p : Fin N × Fin N => p.1 < p.2)
      ((S ×ˢ S).filter fun p : Fin N × Fin N => p.2 < p.1) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact lt_asymm h1.2 h2.2
  have hc := Finset.offDiag_card S
  rw [hoff, Finset.card_union_of_disjoint hdisj, ← hsw] at hc
  have hle : S.card ≤ S.card * S.card := Nat.le_mul_self _
  omega

theorem count_identity {N : ℕ} (S : Finset (Fin N)) :
    2 * ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card + 2 * ∑ a ∈ S, (a : ℕ)
      + S.card * (S.card + 1) = 2 * S.card * N := by
  classical
  have hP := two_mul_card_lt_pairs S
  have hsplit : ((S ×ˢ S).filter fun p : Fin N × Fin N => p.1 < p.2).card
      + ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card
      = ∑ a ∈ S, (Finset.Ioi a).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.sum_product, Finset.sum_product,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_add_sum_compl, ← Finset.card_filter, Finset.filter_lt_eq_Ioi]
  have hterm : ∀ a : Fin N, (Finset.Ioi a).card + (a : ℕ) + 1 = N := by
    intro a
    rw [Fin.card_Ioi]
    have := a.isLt
    omega
  have hsum : ∑ a ∈ S, (Finset.Ioi a).card + ∑ a ∈ S, (a : ℕ) + S.card = S.card * N := by
    have h0 : ∑ a ∈ S, ((Finset.Ioi a).card + (a : ℕ) + 1) = S.card * N := by
      rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_const, smul_eq_mul]
    rwa [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at h0
  nlinarith [hP, hsplit, hsum]

end GlobalTheory.SatakeSubsetSum

namespace GlobalTheory.SatakeSubsetSum

open Finset

theorem prod_zpow_eq {ι : Type} (s : ℂ) (hs : s ≠ 0) (S : Finset ι) (e : ι → ℤ) :
    ∏ a ∈ S, s ^ e a = s ^ (∑ a ∈ S, e a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert b T hb ih => rw [Finset.prod_insert hb, Finset.sum_insert hb, ih, zpow_add₀ hs]

theorem cpow_half_int (q : ℕ) (m : ℤ) :
    (q : ℂ) ^ ((m : ℂ) / 2) = ((Real.sqrt q : ℝ) : ℂ) ^ m := by
  have h1 : ((q : ℝ) : ℂ) ^ ((((m : ℝ) / 2 : ℝ)) : ℂ) = ((((q : ℝ) ^ ((m : ℝ) / 2) : ℝ)) : ℂ) :=
    (Complex.ofReal_cpow (Nat.cast_nonneg q) _).symm
  have h2 : (q : ℝ) ^ ((m : ℝ) / 2) = (Real.sqrt q) ^ m := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    ring_nf
  rw [h2] at h1
  push_cast at h1
  exact h1

theorem borelParam_eq (q N : ℕ) (α : Fin N → ℂˣ) (a : Fin N) :
    borelParam q α a = (α a : ℂ) * ((Real.sqrt q : ℝ) : ℂ) ^ (2 * (a : ℤ) - N + 1) := by
  unfold borelParam
  rw [← cpow_half_int]
  congr 2
  push_cast
  ring

end GlobalTheory.SatakeSubsetSum

namespace GlobalTheory.SatakeSubsetSum

open Finset

theorem term_eq (q N : ℕ) (hq : 0 < q) (α : Fin N → ℂˣ) (S : Finset (Fin N)) :
    (q : ℂ) ^ ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card * ∏ a ∈ S, borelParam q α a
      = ((Real.sqrt q : ℝ) : ℂ) ^ (S.card * (N - S.card)) * ∏ a ∈ S, (α a : ℂ) := by
  set s : ℂ := ((Real.sqrt q : ℝ) : ℂ) with hsdef
  have hs : s ≠ 0 := by
    rw [hsdef, Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
    exact_mod_cast hq
  have hs2 : (q : ℂ) = s ^ 2 := by
    rw [hsdef, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    push_cast; rfl
  have hnN : S.card ≤ N := by
    simpa using Finset.card_le_univ S
  set inv := ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card with hinv
  have hcount := count_identity S
  rw [← hinv] at hcount
  simp_rw [borelParam_eq]
  rw [Finset.prod_mul_distrib, prod_zpow_eq s hs, hs2, ← pow_mul, ← zpow_natCast, ← zpow_natCast,
    mul_left_comm, ← zpow_add₀ hs, mul_comm]
  congr 2
  have hc : ((2 * inv + 2 * ∑ a ∈ S, (a : ℕ) + S.card * (S.card + 1) : ℕ) : ℤ) = ((2 * S.card * N : ℕ) : ℤ) := by
    rw [hcount]
  push_cast at hc
  push_cast [Nat.cast_sub hnN]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul]
  push_cast
  linear_combination hc

end GlobalTheory.SatakeSubsetSum

namespace GlobalTheory.SatakeSubsetSum

open Finset

theorem satake_subset_sum : ∀ (q N : ℕ), 0 < q → ∀ (α : Fin N → ℂˣ) (n : ℕ),
    ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n,
      ((q : ℂ) ^ ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card * ∏ a ∈ S, borelParam q α a)
      = genVal q 0 N (Finset.univ.val.map α) n := by
  intro q N hq α n
  unfold genVal
  rw [Multiset.map_map, Finset.esymm_map_val, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.mem_powersetCard] at hS
  rw [term_eq q N hq α S, hS.2, zero_mul, zero_add]
  rfl

end GlobalTheory.SatakeSubsetSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardOrderSymmInr
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

noncomputable section
namespace GlobalTheory.SymChain.NonZeroAt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Coords
variable {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem typeFrame_bas_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (Sum.elim (fun _ => (1 : k)) fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
  change (fromBlocks 1 0 0 (diagonal _) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) = _
  rw [← diagonal_one, fromBlocks_diagonal]
  congr 1

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem typeFrame_bas_inv_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val =
      diagonal (Sum.elim (fun _ => (1 : k)) fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [typeFrame_bas_val, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rcases i with i | i
  · simp
  · simp [mul_inv_cancel₀, pow_ne_zero]

end Coords

section Ord
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Ord

section Chain
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]


end Chain

section Entry
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

end Entry

section Main
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

end Main

section Final
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

end Final

end GlobalTheory.SymChain.NonZeroAt

namespace GlobalTheory.SymChain

end GlobalTheory.SymChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainOneCouplingCosetOfPattern
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

section SlopeTestRemainingChoices
variable {k : Type} [Field k] {ι ι' n n' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

omit [Fintype ι] [DecidableEq ι] in
theorem typeFrame_bas_zero (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin 0) : (typeFrame ϖ ord).bas = 1 := by
  apply Units.ext
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [typeFrame, embA, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
theorem coords_withCol (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin 0) (ord' : ι' ≃ n' ⊕ Fin (0 + 1)) (x₀ : Matrix n n' k)
    (y : n → k) : (typeFrame ϖ ord).coords (typeFrame ϖ ord') (withCol x₀ y) =
      (withCol x₀ ((ϖ : k) • y)).submatrix ord ord' := by
  unfold LatFrame.coords
  rw [typeFrame_bas_zero]
  congr 1
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [withCol, typeFrame, embA, Matrix.fromBlocks_multiply]
    · simp [withCol, typeFrame, embA, Matrix.fromBlocks_multiply, Fin.eq_zero j, mul_comm]
  · exact i.elim0

variable [ValuativeRel k]

theorem unif_mul_lt_one_iff {ϖ : kˣ} (h : IsUnif ϖ) (z : k) :
    valuation k ((ϖ : k) * z) < 1 ↔ valuation k z ≤ 1 := by
  rw [h, map_mul]
  have h0 : 0 < valuation k (ϖ : k) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr (Units.ne_zero ϖ)
  exact mul_le_iff_le_one_right h0

end SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem SymData.Psi_one_eq (x₀ : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k) (y : XIx (Fin κ) t (s + 1) → k) :
    (S.T t).Psi 1 x₀ y = (S.P.iter t S.μ S.tame s).Phi t (S.μ (s + 1))
      (((withCol x₀ ((S.ϖ : k) • y)).submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl)
        (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix (ixSucc _ t s) id) := by
  simp only [Chain.Psi, om_one, SymData.T, typeChain, Chain.ofType, LatFrame.transport, coords_withCol,
    TypeDatum.iterPhi]

omit [Fintype t] [DecidableEq t] in
theorem not_freeIx_col (ρ : ℕ) {l j : ℕ} (a : Ix (Fin κ ⊕ Fin (l + 1)) t j) :
    ¬ FreeIx ρ a (.inl (.inr 0)) := by
  rcases a with (i | i) | p <;> simp [FreeIx, FreeTop]

omit [Fintype t] [DecidableEq t] in
theorem stdOrd_last (s : ℕ) : stdOrd (Fin κ) t (s + 1) 0 rfl (.inl (.inr 0)) = .inl (.inl (.inr 0)) := by
  simpa using stdOrd_f (Fin κ) t (s + 1) 0 rfl 0

omit [Fintype t] [DecidableEq t] in
theorem stdOrd_pen (s : ℕ) : stdOrd (Fin κ) t s (0 + 1) rfl (.inl (.inr 0)) = .inr 0 := by
  simpa using standardOrderExtendedBasis_apply_low_block (Fin κ) t s (0 + 1) rfl 0

omit [Fintype t] in
theorem SymData.symmetricChain_sub_base_mem_latticeBox_iff (y : XIx (Fin κ) t (s + 1) → k) :
    y - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ) ↔ ∀ i, valuation k ((S.ϖ : k) * y i -
      (1 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k) i (Sum.inl (Sum.inr 0))) < 1 := by
  rw [mem_box]
  refine forall_congr' fun i => ?_
  have e : (S.ϖ : k) * y i - (1 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k) i (Sum.inl (Sum.inr 0)) =
      (S.ϖ : k) * (y - S.y0 t) i := by
    simp only [SymData.y0, Pi.sub_apply, Pi.single_apply, Matrix.one_apply, mul_sub]
    split_ifs <;> simp
  rw [e, unif_mul_lt_one_iff S.unif]
  simp

omit [Fintype t] [DecidableEq t] in
private theorem stdOrd_ixSucc_inl_inr_zero :
    stdOrd (Fin κ) t (s + 1) 0 rfl (ixSucc (Fin κ ⊕ Fin (s + 1)) t s (Sum.inl (Sum.inl (Sum.inr 0)))) =
      Sum.inl (Sum.inl (Sum.inr 0)) := by
  have h : ixSucc (Fin κ ⊕ Fin (s + 1)) t s (Sum.inl (Sum.inl (Sum.inr 0))) = Sum.inl (Sum.inr 0) := rfl
  rw [h, stdOrd_last]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype t] [DecidableEq t] in
private theorem submatrix_withCol_stdOrd_ixSucc_apply_eq (x₀ : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k)
    (w : XIx (Fin κ) t (s + 1) → k) (r : Ix (Fin κ ⊕ Fin (s + 1)) t s ⊕ t) (i : XIx (Fin κ) t (s + 1))
    (hr : stdOrd (Fin κ) t (s + 1) 0 rfl (ixSucc _ t s r) = Sum.inl i) :
    (((withCol x₀ w).submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl) (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix
      (ixSucc _ t s) id) r (Sum.inl (Sum.inr 0)) = w i := by
  simp only [Matrix.submatrix_apply, id, hr, stdOrd_pen, withCol, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]

private theorem sub_y0_mem_box_of_psi_ne_zero (hP : S.Pattern t)
    (x₀ : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k) (y : XIx (Fin κ) t (s + 1) → k)
    (h : (S.T t).Psi 1 x₀ y ≠ 0) : y - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ) := by
  rw [S.Psi_one_eq t x₀ y] at h
  have hent := submatrix_withCol_stdOrd_ixSucc_apply_eq t x₀ ((S.ϖ : k) • y)
  generalize hX : ((withCol x₀ ((S.ϖ : k) • y)).submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl)
    (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix (ixSucc _ t s) id = X at h hent
  obtain ⟨⟨g, hgJ, hg⟩, hmax⟩ := (TypeDatum.Phi_ne_zero_iff _ _).mp h
  rw [hP s g] at hgJ
  rw [S.symmetricChain_sub_base_mem_latticeBox_iff t y]
  intro i
  set b' : Ix (Fin κ ⊕ Fin (s + 1)) t s := Sum.inl (Sum.inr 0) with hb'
  set r := (ixSucc _ t s).symm ((stdOrd (Fin κ) t (s + 1) 0 rfl).symm (Sum.inl i)) with hrdef
  have hr : stdOrd (Fin κ) t (s + 1) 0 rfl (ixSucc _ t s r) = Sum.inl i := by simp [r]
  have hf := stdOrd_ixSucc_inl_inr_zero (κ := κ) t (s := s)
  have key : i = Sum.inl (Sum.inr 0) ↔ r = Sum.inl b' := by
    constructor
    · intro hi
      apply (ixSucc _ t s).injective
      apply (stdOrd (Fin κ) t (s + 1) 0 rfl).injective
      rw [hr, hf, hi]
    · intro hrb
      rw [hrb, hf] at hr
      exact (Sum.inl_injective hr).symm
  have hv := hent r i hr
  clear_value r
  rcases r with a | τ
  · have h1 := hgJ.2 a b' (not_freeIx_col t S.ρ a)
    have hga : g.val a b' = (S.ϖ : k) * y i := by
      rw [hg]
      exact hv
    rw [hga] at h1
    have h1' : (1 : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t s) (Ix (Fin κ ⊕ Fin (s + 1)) t s) k) a b' =
        (1 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k) i (Sum.inl (Sum.inr 0)) := by
      simp only [Matrix.one_apply, key, Sum.inl.injEq]
    rwa [h1'] at h1
  · have h1 := hmax τ b'
    have hne : i ≠ Sum.inl (Sum.inr 0) := fun hi => by simpa using key.mp hi
    have hbot : X.toRows₂ τ b' = (S.ϖ : k) * y i := hv
    rw [hbot] at h1
    simpa [Matrix.one_apply, hne] using h1

private theorem psi_eq_psi_y0_of_sub_y0_mem_box (x₀ : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k) (y : XIx (Fin κ) t (s + 1) → k)
    (hy : y - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ)) :
    (S.T t).Psi 1 x₀ y = (S.T t).Psi 1 x₀ (S.y0 t) := by
  rw [S.Psi_one_eq t x₀ y, S.Psi_one_eq t x₀ (S.y0 t)]
  have hsplit : withCol x₀ ((S.ϖ : k) • y) =
      withCol x₀ ((S.ϖ : k) • S.y0 t) + withCol 0 ((S.ϖ : k) • (y - S.y0 t)) := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [withCol]
      · simp [withCol]
        ring
    · exact i.elim0
  have hw : ∀ a b, valuation k (withCol (0 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k)
      ((S.ϖ : k) • (y - S.y0 t)) a b) < 1 := by
    rintro (a | a) (b | b)
    · simp [withCol]
    · simp only [withCol, Matrix.fromBlocks_apply₁₂, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      exact (unif_mul_lt_one_iff S.unif _).mpr (by simpa using (mem_box.mp hy) a)
    · exact a.elim0
    · exact a.elim0
  rw [hsplit]
  have hsum : (((withCol x₀ ((S.ϖ : k) • S.y0 t) + withCol 0 ((S.ϖ : k) • (y - S.y0 t))).submatrix
      (stdOrd (Fin κ) t (s + 1) 0 rfl) (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix (ixSucc _ t s) id) =
      ((withCol x₀ ((S.ϖ : k) • S.y0 t)).submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl)
        (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix (ixSucc _ t s) id +
      ((withCol 0 ((S.ϖ : k) • (y - S.y0 t))).submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl)
        (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix (ixSucc _ t s) id := by
    ext i j
    rfl
  rw [hsum]
  exact TypeDatum.Phi_add _ (S.tame (s + 1)) _ (fun i j => hw _ _)

private theorem mulVec_y0_sub_y0_mem_box_of_embX_mem_J (hP : S.Pattern t) (γ : GL (XIx (Fin κ) t (s + 1)) k)
    (hγ : embX 0 γ ∈ ((S.T t).lev (s + 1) 0 rfl).J) :
    γ.val *ᵥ S.y0 t - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ) := by
  have h1 : (typeFrame S.ϖ (stdOrd (Fin κ) t (s + 1) 0 rfl)).conj.symm (embX 0 γ) ∈
      (S.P.iter t S.μ S.tame (s + 1)).J := Level.mem_map.mp hγ
  rw [hP] at h1
  have hval : ((typeFrame S.ϖ (stdOrd (Fin κ) t (s + 1) 0 rfl)).conj.symm (embX 0 γ)).val =
      (embX 0 γ).val.submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl) (stdOrd (Fin κ) t (s + 1) 0 rfl) := by
    rw [LatFrame.conj, MulEquiv.symm_trans_apply, typeFrame_bas_zero, MulAut.conj_symm_apply, inv_one, one_mul,
      mul_one, reGL_symm_val]
    rfl
  rw [mem_box]
  intro i
  set b' : Ix (Fin κ ⊕ Fin (s + 1)) t (s + 1) := Sum.inl (Sum.inr 0) with hb'
  have hb : stdOrd (Fin κ) t (s + 1) 0 rfl b' = Sum.inl (Sum.inl (Sum.inr 0)) := stdOrd_last t s
  set a := (stdOrd (Fin κ) t (s + 1) 0 rfl).symm (Sum.inl i) with ha
  have hai : stdOrd (Fin κ) t (s + 1) 0 rfl a = Sum.inl i := by simp [a]
  have h2 := h1.2 a b' (not_freeIx_col t S.ρ a)
  rw [hval, Matrix.submatrix_apply, hai, hb] at h2
  have hone : (1 : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 1)) (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 1)) k) a b' =
      (1 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k) i (Sum.inl (Sum.inr 0)) := by
    have : a = b' ↔ i = Sum.inl (Sum.inr 0) := by
      rw [← (stdOrd (Fin κ) t (s + 1) 0 rfl).apply_eq_iff_eq, hai, hb, Sum.inl.injEq]
    simp only [Matrix.one_apply, this]
  rw [hone] at h2
  have hemb : (embX 0 γ).val (Sum.inl i) (Sum.inl (Sum.inl (Sum.inr 0))) = γ.val i (Sum.inl (Sum.inr 0)) := by
    simp [embX]
  rw [hemb] at h2
  have hvec : (γ.val *ᵥ S.y0 t - S.y0 t) i =
      (γ.val i (Sum.inl (Sum.inr 0)) - (1 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k) i
        (Sum.inl (Sum.inr 0))) * ((S.ϖ⁻¹ : kˣ) : k) := by
    simp only [SymData.y0, Matrix.mulVec_single, Pi.sub_apply, Pi.single_apply, Matrix.one_apply, sub_mul]
    split_ifs <;> simp
  rw [hvec, map_mul, Units.val_one, map_one]
  have hu : valuation k ((S.ϖ⁻¹ : kˣ) : k) = (valuation k (S.ϖ : k))⁻¹ := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
  rw [hu, ← div_eq_mul_inv, div_le_one₀ (by
    rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr (Units.ne_zero S.ϖ))]
  exact (S.unif _).mp h2

theorem SymData.oneCoupling_of_pattern (hP : S.Pattern t) : S.OneCoupling t := by
  exact ⟨fun x₀ y h => sub_y0_mem_box_of_psi_ne_zero S t hP x₀ y h,
    fun x₀ y hy => psi_eq_psi_y0_of_sub_y0_mem_box S t x₀ y hy,
    fun γ hγ => mulVec_y0_sub_y0_mem_box_of_embX_mem_J S t hP γ hγ⟩

theorem oneCoupling : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.OneCoupling t := by
  intro k _ _ _ _ s κ S t _ _ hP
  exact S.oneCoupling_of_pattern t hP

end GlobalTheory.SymChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricPositionLevelCharacterEqOneSingleRowStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionLevel_character_eq_one_single_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (ρ κ l : ℕ) (P : TypeDatum k (Fin κ ⊕ Fin l)), GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P → ∀ (i₀ : Fin l) (g : P.J), (∀ a b, a ≠ Sum.inr i₀ → (g : GL (Fin κ ⊕ Fin l) k).val a b = (1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) a b) → (∀ i : Fin l, i.val = i₀.val + 1 → (g : GL (Fin κ ⊕ Fin l) k).val (Sum.inr i₀) (Sum.inr i) = 0) → P.lam g = 1 := by
  intro k _ _ _ _ ψ ϖ ρ κ l P hP i₀ g h1 h2
  have hs : simpleSum (g : GL (Fin κ ⊕ Fin l) k) = 0 := by
    unfold simpleSum
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hij
    · by_cases hi : i = i₀
      · subst hi; exact h2 j hij
      · have hne : i ≠ j := by
          intro e; subst e; omega
        rw [h1 _ _ (by simpa using hi)]
        simp [hne]
    · rfl
  have hu : superSum Fin.val (g : GL (Fin κ ⊕ Fin l) k).val.toBlocks₁₁ = 0 := by
    unfold superSum
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hab
    · have hne : a ≠ b := by
        intro e; subst e; omega
      rw [Matrix.toBlocks₁₁]
      simp only [Matrix.of_apply]
      rw [h1 _ _ (by simp)]
      simp [hne]
    · rfl
  apply Units.ext
  rw [hP.2 g, hs, hu]
  simp

end

