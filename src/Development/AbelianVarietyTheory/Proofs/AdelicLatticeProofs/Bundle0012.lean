module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GramMinorSwapAdjacentColumns
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

private theorem exch_sum_split {N : ℕ} (p q : Fin N) (hq : (q : ℕ) = p + 1) (f : Fin N → ℝ)
    (hf : ∀ r, q < r → f r = 0) :
    ∑ r, f r = ∑ r ∈ Finset.univ.filter (· < p), f r + (f p + f q) := by
  have hpq : p ≠ q := fun e => by have := congrArg Fin.val e; omega
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· < p)]
  congr 1
  have hsub : ({p, q} : Finset (Fin N)) ⊆ Finset.univ.filter (fun r => ¬ r < p) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Fin.le_def]
    rcases hx with rfl | rfl <;> omega
  rw [← Finset.sum_subset hsub, Finset.sum_pair hpq]
  intro x hx hx'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Fin.le_def] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'
  apply hf
  rw [Fin.lt_def]
  have h1 : (x : ℕ) ≠ p := fun e => hx'.1 (Fin.ext e)
  have h2 : (x : ℕ) ≠ q := fun e => hx'.2 (Fin.ext e)
  omega

private theorem det_updateRow_last_single_eq_mul_det_submatrix {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (x : ℝ) :
    (X.updateRow (Fin.last m) (Pi.single (Fin.last m) x)).det =
      x * (X.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row _ (Fin.last m), Finset.sum_eq_single (Fin.last m)]
  · have hsub : (X.updateRow (Fin.last m) (Pi.single (Fin.last m) x)).submatrix
        (Fin.last m).succAbove (Fin.last m).succAbove = X.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_last]
      rw [Matrix.updateRow_ne (Fin.castSucc_lt_last i).ne]
    rw [hsub, Matrix.updateRow_self, Pi.single_eq_same, Fin.val_last, Even.neg_one_pow ⟨m, rfl⟩, one_mul]
  · intro j _ hj
    rw [Matrix.updateRow_self, Pi.single_eq_of_ne hj, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem gram_minor_swap_columns : ∀ (N : ℕ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n g g' : Matrix (Fin N) (Fin N) ℝ) (p q : Fin N), kᵀ * k = 1 → (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → (q : ℕ) = p + 1 → g = k * diagonal a * n → g' = g.submatrix id (Equiv.swap p q) → (∀ (j : ℕ) (h : j ≤ N), j ≠ q → ((g'ᵀ * g').submatrix (Fin.castLE h) (Fin.castLE h)).det = ((gᵀ * g).submatrix (Fin.castLE h) (Fin.castLE h)).det) ∧ ∀ h : (q : ℕ) ≤ N, ((g'ᵀ * g').submatrix (Fin.castLE h) (Fin.castLE h)).det = (∏ l ∈ Finset.univ.filter (· < p), a l ^ 2) * (a q ^ 2 + n p q ^ 2 * a p ^ 2) := by
  intro N k a n g g' p q hk hn1 hn0 hq hg hg'

  have hG : gᵀ * g = (diagonal a * n)ᵀ * (diagonal a * n) := by
    rw [hg]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc kᵀ k, hk, Matrix.one_mul]
  have hG' : g'ᵀ * g' = (gᵀ * g).submatrix (Equiv.swap p q) (Equiv.swap p q) := by
    rw [hg']
    ext i j
    simp [Matrix.mul_apply]
  rw [hG', hG]
  set M : Matrix (Fin N) (Fin N) ℝ := diagonal a * n with hM
  have hMe : ∀ i j, M i j = a i * n i j := fun i j => by simp [hM, Matrix.diagonal_mul]
  have hMl : ∀ i j, j < i → M i j = 0 := fun i j h => by rw [hMe, hn0 i j h, mul_zero]
  have hMd : ∀ i, M i i = a i := fun i => by rw [hMe, hn1, mul_one]
  refine ⟨fun j hj hjq => ?_, fun h => ?_⟩
  · by_cases hjp : j ≤ (p : ℕ)
    ·
      congr 1
      have hfix : ∀ z : Fin j, Equiv.swap p q (Fin.castLE hj z) = Fin.castLE hj z := by
        intro z
        have hz := z.isLt
        apply Equiv.swap_apply_of_ne_of_ne
        · intro e
          have := congrArg Fin.val e
          simp only [Fin.coe_castLE] at this
          omega
        · intro e
          have := congrArg Fin.val e
          simp only [Fin.coe_castLE] at this
          omega
      ext x y
      simp only [Matrix.submatrix_apply, hfix]
    ·
      have hpj : (p : ℕ) < j := by omega
      have hqj : (q : ℕ) < j := by omega
      have e1 : Fin.castLE hj ⟨p, hpj⟩ = p := Fin.ext rfl
      have e2 : Fin.castLE hj ⟨q, hqj⟩ = q := Fin.ext rfl
      have hs : ∀ z : Fin j, Equiv.swap p q (Fin.castLE hj z) =
          Fin.castLE hj (Equiv.swap ⟨p, hpj⟩ ⟨q, hqj⟩ z) := by
        intro z
        have := (Fin.castLE_injective hj).swap_apply ⟨p, hpj⟩ ⟨q, hqj⟩ z
        rwa [e1, e2] at this
      have hsub : ((Mᵀ * M).submatrix (Equiv.swap p q) (Equiv.swap p q)).submatrix (Fin.castLE hj)
          (Fin.castLE hj) = ((Mᵀ * M).submatrix (Fin.castLE hj) (Fin.castLE hj)).submatrix
          (Equiv.swap (⟨p, hpj⟩ : Fin j) ⟨q, hqj⟩) (Equiv.swap (⟨p, hpj⟩ : Fin j) ⟨q, hqj⟩) := by
        ext x y
        simp only [Matrix.submatrix_apply, hs]
      rw [hsub, Matrix.det_submatrix_equiv_self]
  · obtain ⟨p, hp⟩ := p
    obtain ⟨q, hqN⟩ := q
    change q = p + 1 at hq
    subst hq
    have h' : p + 1 ≤ N := h
    set P : Fin N := ⟨p, hp⟩ with hP
    set Q : Fin N := ⟨p + 1, hqN⟩ with hQ
    set σ := Equiv.swap P Q with hσ
    set c : Fin (p + 1) → Fin N := Fin.castLE h' with hc
    show (((Mᵀ * M).submatrix σ σ).submatrix c c).det = _
    have hcl : c (Fin.last p) = P := Fin.ext rfl
    have hσc : ∀ s : Fin (p + 1), s ≠ Fin.last p → σ (c s) = c s := by
      intro s hs
      have h1 : (s : ℕ) < p := by
        have := s.isLt
        have : (s : ℕ) ≠ p := fun e => hs (Fin.ext e)
        omega
      apply Equiv.swap_apply_of_ne_of_ne
      · intro e
        have := congrArg Fin.val e
        change (s : ℕ) = p at this
        omega
      · intro e
        have := congrArg Fin.val e
        change (s : ℕ) = p + 1 at this
        omega
    have hσl : σ (c (Fin.last p)) = Q := by
      rw [hcl]
      exact Equiv.swap_apply_left P Q
    have hle : ∀ s, σ (c s) ≤ Q := by
      intro s
      by_cases hs : s = Fin.last p
      · rw [hs, hσl]
      · rw [hσc s hs, Fin.le_def]
        change (s : ℕ) ≤ p + 1
        have := s.isLt
        omega

    set B : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ := Matrix.of fun s i => M (c s) (σ (c i)) with hB
    have hBe : ∀ s i, B s i = M (c s) (σ (c i)) := fun s i => rfl
    set emb : Fin p ↪ Fin N :=
      ⟨fun i : Fin p => c i.castSucc, fun x y e => by simpa [Fin.ext_iff, hc] using e⟩ with hemb
    have hembx : ∀ x, emb x = c x.castSucc := fun x => rfl
    have hfilt : Finset.univ.filter (· < P) = (Finset.univ : Finset (Fin p)).map emb := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro hl
        exact ⟨⟨l, hl⟩, Fin.ext rfl⟩
      · rintro ⟨i, _, rfl⟩
        exact i.isLt

    have hX : ((Mᵀ * M).submatrix σ σ).submatrix c c =
        (Bᵀ * B).updateRow (Fin.last p) ((Bᵀ * B) (Fin.last p) + Pi.single (Fin.last p) (a Q ^ 2)) := by
      ext i j
      have hsum : (((Mᵀ * M).submatrix σ σ).submatrix c c) i j =
          (Bᵀ * B) i j + M Q (σ (c i)) * M Q (σ (c j)) := by
        simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, hBe]
        rw [exch_sum_split P Q rfl _ (fun r hr => by rw [hMl r _ (lt_of_le_of_lt (hle i) hr), zero_mul]),
          Fin.sum_univ_castSucc, hfilt, Finset.sum_map, hcl]
        simp only [hembx]
        ring
      rw [hsum]
      by_cases hi : i = Fin.last p
      · subst hi
        rw [Matrix.updateRow_self, Pi.add_apply]
        by_cases hj : j = Fin.last p
        · subst hj
          rw [hσl, hMd, Pi.single_eq_same]
          ring
        · rw [hσl, hσc j hj, hMl Q (c j) (Fin.lt_def.2 j.isLt), mul_zero, Pi.single_eq_of_ne hj]
      · rw [Matrix.updateRow_ne hi, hσc i hi, hMl Q (c i) (Fin.lt_def.2 i.isLt), zero_mul, add_zero]
    have hBT : B.BlockTriangular id := by
      intro s i hi
      have hil : i ≠ Fin.last p := fun e => by
        rw [e] at hi
        exact (not_lt.2 (Fin.le_last s)) hi
      rw [hBe, hσc i hil]
      exact hMl _ _ (Fin.lt_def.2 (Fin.lt_def.1 hi))
    have hdB : B.det = (∏ i : Fin p, a (c i.castSucc)) * (a P * n P Q) := by
      rw [Matrix.det_of_upperTriangular hBT, Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        rw [hBe, hσc _ (Fin.castSucc_lt_last i).ne, hMd]
      · rw [hBe, hσl, hcl, hMe]
    have hminor : (Bᵀ * B).submatrix Fin.castSucc Fin.castSucc =
        (B.submatrix Fin.castSucc Fin.castSucc)ᵀ * B.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
      rw [Fin.sum_univ_castSucc]
      have hz : B (Fin.last p) i.castSucc = 0 := by
        rw [hBe, hσc _ (Fin.castSucc_lt_last i).ne, hcl]
        exact hMl _ _ (Fin.lt_def.2 (Fin.lt_def.1 (Fin.castSucc_lt_last i)))
      rw [hz, zero_mul, add_zero]
    have hBT' : (B.submatrix Fin.castSucc Fin.castSucc).BlockTriangular id := by
      intro s i hi
      exact hBT (Fin.castSucc_lt_castSucc_iff.2 hi)
    have hdB' : (B.submatrix Fin.castSucc Fin.castSucc).det = ∏ i : Fin p, a (c i.castSucc) := by
      rw [Matrix.det_of_upperTriangular hBT']
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Matrix.submatrix_apply, hBe, hσc _ (Fin.castSucc_lt_last i).ne, hMd]
    have hprod : ∏ l ∈ Finset.univ.filter (· < P), a l ^ 2 = (∏ i : Fin p, a (c i.castSucc)) ^ 2 := by
      rw [hfilt, Finset.prod_map, ← Finset.prod_pow]
      simp only [hembx]
    rw [hX, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, det_updateRow_last_single_eq_mul_det_submatrix, hminor,
      Matrix.det_mul, Matrix.det_transpose, Matrix.det_mul, Matrix.det_transpose, hdB, hdB', hprod]
    ring

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HilbertFinitenessLeftInvariantMatrixPoly
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.HilbertFin

open MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    evC (ltr g f) y = evC f (g * y) := by
  unfold evC ltr
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp]
    simp [Matrix.mul_apply]

omit [DecidableEq ι] in
theorem isInv_iff (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ) :
    IsInv Γ f ↔ ∀ g ∈ Γ, ltr g f = f := by
  constructor
  · intro h g hg
    apply MvPolynomial.funext
    intro x
    have := h g hg (Matrix.of fun i j => x (i, j))
    rw [← evC_ltr] at this
    exact this
  · intro h g hg y
    rw [← evC_ltr, h g hg]

omit [DecidableEq ι] in
theorem ltr_homog (g : Matrix ι ι ℂ) {f : MvPolynomial (ι × ι) ℂ} {n : ℕ}
    (hf : f.IsHomogeneous n) : (ltr g f).IsHomogeneous n := by
  have := hf.aeval (fun ij : ι × ι => ∑ k, MvPolynomial.C (g ij.1 k) * (MvPolynomial.X (k, ij.2) : MvPolynomial (ι × ι) ℂ))
    (n := 1) (fun ij => IsHomogeneous.sum _ _ _ fun k _ => by
      simpa using (isHomogeneous_C (ι × ι) (g ij.1 k)).mul (isHomogeneous_X ℂ (k, ij.2)))
  rw [one_mul] at this
  exact this

omit [DecidableEq ι] in
theorem ltr_comp (g : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) (n : ℕ) :
    ltr g (homogeneousComponent n f) = homogeneousComponent n (ltr g f) := by
  conv_lhs => rw [← sum_homogeneousComponent f]
  conv_rhs => rw [← sum_homogeneousComponent f]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := homogeneousComponent_isHomogeneous i f
  rw [homogeneousComponent_of_mem h1, homogeneousComponent_of_mem (ltr_homog g h1)]
  split_ifs <;> simp

omit [DecidableEq ι] in
theorem isInv_comp {Γ : Set (Matrix ι ι ℂ)} {f : MvPolynomial (ι × ι) ℂ} (hf : IsInv Γ f) (n : ℕ) :
    IsInv Γ (homogeneousComponent n f) := by
  rw [isInv_iff] at hf ⊢
  intro g hg
  rw [ltr_comp, hf g hg]

theorem hilbert_finiteness : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ), IsReynolds Γ Rey → ∃ s : Finset (MvPolynomial (ι × ι) ℂ), (∀ F ∈ s, IsInv Γ F ∧ ∃ n, F.IsHomogeneous n) ∧ ∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (s : Set (MvPolynomial (ι × ι) ℂ)) := by
  intro ι _ _ Γ Rey hR
  classical
  set S : Set (MvPolynomial (ι × ι) ℂ) := {F | IsInv Γ F ∧ ∃ n, 0 < n ∧ F.IsHomogeneous n} with hS
  have hfg : (Submodule.span (MvPolynomial (ι × ι) ℂ) S).FG := IsNoetherian.noetherian _
  obtain ⟨s, hsS, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).1 hfg
  refine ⟨s, fun F hF => ⟨(hsS hF).1, (hsS hF).2.imp fun n h => h.2⟩, ?_⟩
  have key : ∀ n : ℕ, ∀ f, IsInv Γ f → f.IsHomogeneous n →
      f ∈ Algebra.adjoin ℂ (s : Set (MvPolynomial (ι × ι) ℂ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hf hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · have : f = C (AddMonoidAlgebra.coeff f 0) := by
          rw [← homogeneousComponent_zero, homogeneousComponent_of_mem hn, if_pos rfl]
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
      · have hmem : f ∈ Submodule.span (MvPolynomial (ι × ι) ℂ) (s : Set (MvPolynomial (ι × ι) ℂ)) := by
          rw [← hs]
          exact Submodule.subset_span ⟨hf, n, hpos, hn⟩
        obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 hmem
        have h1 : f = ∑ F ∈ s, F * Rey (c F) := by
          set_option synthInstance.maxHeartbeats 100000 in
            conv_lhs => rw [← hR.fix f hf, ← hc, map_sum]
          refine Finset.sum_congr rfl fun F hF => ?_
          rw [smul_eq_mul, mul_comm, hR.mul _ _ (hsS hF).1]
        have h2 : f = homogeneousComponent n f := by
          rw [homogeneousComponent_of_mem hn, if_pos rfl]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [h2, h1, map_sum]
        refine Subalgebra.sum_mem _ fun F hF => ?_
        obtain ⟨-, d, hd, hFd⟩ := hsS hF
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← sum_homogeneousComponent (Rey (c F)), Finset.mul_sum, map_sum]
        refine Subalgebra.sum_mem _ fun i _ => ?_
        have h3 := homogeneousComponent_isHomogeneous i (Rey (c F))
        rw [homogeneousComponent_of_mem (hFd.mul h3)]
        split_ifs with h
        · exact Subalgebra.mul_mem _ (Algebra.subset_adjoin hF)
            (ih i (by omega) _ (isInv_comp (hR.inv _) i) h3)
        · exact Subalgebra.zero_mem _
  intro f hf
  rw [← sum_homogeneousComponent f]
  exact Subalgebra.sum_mem _ fun i _ =>
    key i _ (isInv_comp hf i) (homogeneousComponent_isHomogeneous i f)

end GlobalTheory.ClassFin.HilbertFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexSqsTopOfFg
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem index_double_prod (L T : Type) [AddCommGroup L] [AddCommGroup T] [Module.Free ℤ L]
    [Module.Finite ℤ L] [Finite T] :
    (nsmulAddMonoidHom (α := L × T) 2).range.index =
      2 ^ Module.finrank ℤ (L × T) * Nat.card (nsmulAddMonoidHom (α := L × T) 2).ker := by
  have h1 : (nsmulAddMonoidHom (α := L × T) 2).range =
      ((nsmulAddMonoidHom (α := L) 2).range).prod (nsmulAddMonoidHom (α := T) 2).range := by
    ext ⟨x, y⟩
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_prod, nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨⟨a, b⟩, h⟩
      exact ⟨⟨a, congrArg Prod.fst h⟩, ⟨b, congrArg Prod.snd h⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨(a, b), Prod.ext ha hb⟩
  have h2 : (nsmulAddMonoidHom (α := L × T) 2).ker =
      (⊥ : AddSubgroup L).prod (nsmulAddMonoidHom (α := T) 2).ker := by
    ext ⟨x, y⟩
    have hx : 2 • x = 0 ↔ x = 0 := by
      rw [← natCast_zsmul, smul_eq_zero]; simp
    simp [AddMonoidHom.mem_ker, AddSubgroup.mem_prod, hx]
  have h3 : Module.finrank ℤ (L × T) = Module.finrank ℤ L := by
    have hT : Module.rank ℤ T = 0 := by
      rw [rank_eq_zero_iff]
      intro x
      refine ⟨(Nat.card T : ℤ), by exact_mod_cast Nat.card_pos.ne', ?_⟩
      simp
    have hq := Submodule.rank_quotient_add_rank (LinearMap.ker (LinearMap.fst ℤ L T))
    have e1 := (LinearMap.quotKerEquivOfSurjective (LinearMap.fst ℤ L T)
      LinearMap.fst_surjective).rank_eq
    have e2 : Module.rank ℤ (LinearMap.ker (LinearMap.fst ℤ L T)) = 0 := by
      rw [LinearMap.ker_fst, rank_range_of_injective _ LinearMap.inr_injective, hT]
    unfold Module.finrank
    rw [← hq, e1, e2, add_zero]
  have h4 : (nsmulAddMonoidHom (α := T) 2).range.index =
      Nat.card (nsmulAddMonoidHom (α := T) 2).ker := by
    have a := AddSubgroup.card_mul_index (nsmulAddMonoidHom (α := T) 2).range
    have b := AddSubgroup.card_mul_index (nsmulAddMonoidHom (α := T) 2).ker
    rw [AddSubgroup.index_ker] at b
    have hpos : 0 < Nat.card (nsmulAddMonoidHom (α := T) 2).range := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [a, mul_comm, b]
  rw [h1, h2, h3, AddSubgroup.index_prod, AddSubgroup.index_range_nsmul, h4,
    Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
  simp

theorem index_double_of_fg (M : Type) [AddCommGroup M] [AddGroup.FG M] :
    (nsmulAddMonoidHom (α := M) 2).range.index =
      2 ^ Module.finrank ℤ M * Nat.card (nsmulAddMonoidHom (α := M) 2).ker := by
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) :=
    Finite.of_equiv _ (DFinsupp.equivFunOnFintype).symm
  have h := index_double_prod (Fin n →₀ ℤ) (DirectSum ι fun i => ZMod (p i ^ e i))
  rw [← AddSubgroup.index_map_equiv _ f, AddEquiv.map_range_nsmulAddMonoidHom, h,
    f.toIntLinearEquiv.finrank_eq]
  congr 1
  refine Nat.card_congr (f.toEquiv.subtypeEquiv ?_).symm
  intro a
  simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
  change _ ↔ 2 • f a = 0
  rw [← map_nsmul, f.map_eq_zero_iff]

theorem index_sqs_top_of_fg : ∀ (G : Type) [CommGroup G] [Group.FG G],
    (sqs (⊤ : Subgroup G)).index =
      2 ^ Module.finrank ℤ (Additive G) * Nat.card {a : G // a ^ 2 = 1} := by
  intro G _ _
  have h := index_double_of_fg (Additive G)
  have h1 : (sqs (⊤ : Subgroup G)).toAddSubgroup =
      (nsmulAddMonoidHom (α := Additive G) 2).range := by
    ext x
    simp only [sqs, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨y, -, hy⟩
      exact ⟨Additive.ofMul y, hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨Additive.toMul y, trivial, hy⟩
  rw [← Subgroup.index_toAddSubgroup, h1, h]
  congr 1

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexSquaresLeTwoMulUnitsSquares
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem mem_hiUnits_sup_sqs_of_even {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) (p : Kˣ)
    (hp : w (p : K) = WithZero.exp (-1)) (x : Kˣ) (m : ℤ)
    (hx : w (x : K) = WithZero.exp (2 * m)) :
    x ∈ hiUnits w 0 ⊔ sqs (⊤ : Subgroup Kˣ) := by
  have h1 : w ((x * (p ^ m) ^ 2 : Kˣ) : K) = 1 := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, map_mul, map_pow,
      map_zpow₀, hx, hp, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add,
      ← WithZero.exp_zero]
    congr 1
    simp
  have hU : x * (p ^ m) ^ 2 ∈ hiUnits w 0 := by
    refine ⟨h1, ?_⟩
    refine le_trans (w.map_sub _ _) (max_le ?_ ?_)
    · rw [h1]; simp
    · simp
  have hS : ((p ^ m)⁻¹) ^ 2 ∈ sqs (⊤ : Subgroup Kˣ) := ⟨(p ^ m)⁻¹, trivial, rfl⟩
  have : x = (x * (p ^ m) ^ 2) * ((p ^ m)⁻¹) ^ 2 := by
    rw [mul_assoc, ← mul_pow, mul_inv_cancel, one_pow, mul_one]
  rw [this]
  exact Subgroup.mul_mem_sup hU hS

theorem index_sqs_top_le : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K),
    w π = WithZero.exp (-1) → (sqs (hiUnits w 0)).relIndex (hiUnits w 0) ≠ 0 →
    (sqs (⊤ : Subgroup Kˣ)).index ≠ 0 ∧
      (sqs (⊤ : Subgroup Kˣ)).index ≤ 2 * (sqs (hiUnits w 0)).relIndex (hiUnits w 0) := by
  intro K _ w π hπ h0
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hdvd : (hiUnits w 0 ⊔ sqs (⊤ : Subgroup Kˣ)).index ∣ 2 := by
    rw [Subgroup.index_dvd_two_iff]
    refine ⟨Units.mk0 π hπ0, fun b => ?_⟩
    have hb : w (b : K) ≠ 0 := by simp
    have hb' : w (b : K) = WithZero.exp (WithZero.log (w (b : K))) := (WithZero.exp_log hb).symm
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' (WithZero.log (w (b : K)))
    · right
      exact mem_hiUnits_sup_sqs_of_even w (Units.mk0 π hπ0) hπ b m (by rw [hb', hm])
    · left
      refine mem_hiUnits_sup_sqs_of_even w (Units.mk0 π hπ0) hπ _ m ?_
      rw [Units.val_mul, map_mul, hb', hm, Units.val_mk0, hπ, ← WithZero.exp_add]
      congr 1
      ring
  have hmul := Subgroup.relIndex_mul_index
    (le_sup_right : sqs (⊤ : Subgroup Kˣ) ≤ hiUnits w 0 ⊔ sqs (⊤ : Subgroup Kˣ))
  rw [Subgroup.relIndex_sup_right] at hmul
  have hle : sqs (hiUnits w 0) ≤ sqs (⊤ : Subgroup Kˣ) := Subgroup.map_mono le_top
  have hd2 := Subgroup.relIndex_dvd_of_le_left (hiUnits w 0) hle
  have hd : (sqs (⊤ : Subgroup Kˣ)).index ∣ 2 * (sqs (hiUnits w 0)).relIndex (hiUnits w 0) := by
    rw [← hmul, mul_comm]
    exact Nat.mul_dvd_mul hdvd hd2
  have hpos : 2 * (sqs (hiUnits w 0)).relIndex (hiUnits w 0) ≠ 0 := mul_ne_zero two_ne_zero h0
  exact ⟨ne_zero_of_dvd_ne_zero hpos hd, Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hd⟩

end GlobalTheory.QNorm
end

