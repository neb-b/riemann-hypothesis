module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCharacterBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Comb

noncomputable section

theorem symmetricGroupCharacter_eq_cf {m : ℕ} (lam : Fin m → ℕ) (rho : List ℕ) :
    symmetricGroupCharacter lam rho = cf (fun i => lam i + stair m i) (alternantPsum m rho) :=
  rfl

theorem CharacterBound.proof (h1 : CombTableEqWords.Statement) (h2 : CombCfBound.Statement) :
    CharacterBound.Statement := by
  intro m lam rho hlam hrho
  rw [symmetricGroupCharacter_eq_cf]
  refine (h2 m rho hrho lam hlam).trans ?_
  by_cases hs : ∑ i, lam i = rho.sum
  · rw [h1 m lam hlam, hs]
  · rw [latticeWords_eq_empty_of_sum_ne _ _ hs, Finset.card_empty, Nat.cast_zero]
    exact Nat.cast_nonneg _

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfAtStair
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

theorem Comb.stair_strictAnti (m : ℕ) : StrictAnti (stair m) := by
  intro a b hab
  have hb := b.isLt
  have hab' : (a : ℕ) < b := hab
  simp only [stair]
  omega

theorem CombCfAtStair.proof (h1 : CombCfUpdateZero.Statement) : CombCfAtStair.Statement := by
  intro m n
  induction n with
  | zero =>
    intro lam hlam
    have hs := Comb.stair_strictAnti m
    have hl : StrictAnti (fun i => lam i + stair m i) := by
      intro a b hab
      have h2 := hlam hab.le
      have h3 := hs hab
      simp only
      omega
    simp only [alternantPsum, List.replicate_zero, List.map_nil, List.prod_nil, mul_one,
      vandermondeOf_X_eq_alt]
    rw [cf_alt_of_strictAnti hl hs]
    by_cases h0 : lam = 0
    · subst h0
      have hu : latticeWords 0 (0 : Fin m → ℕ) = univ := by
        rw [Finset.eq_univ_iff_forall]
        intro w
        simp only [latticeWords, mem_filter, mem_univ, true_and]
        refine ⟨fun t ht i j _ => ?_, fun i => pcnt_zero w i⟩
        have ht0 : t = 0 := by omega
        subst ht0
        rw [pcnt_zero, pcnt_zero]
      rw [hu, Finset.card_univ]
      simp
    · have hne : (fun i => lam i + stair m i) ≠ stair m := by
        intro h
        apply h0
        funext i
        have := congrFun h i
        show lam i = 0
        omega
      rw [if_neg hne, latticeWords_eq_empty_of_sum_ne]
      · simp
      · intro hsum
        apply h0
        funext i
        have := (Finset.sum_eq_zero_iff.mp hsum) i (mem_univ i)
        simpa using this
  | succ n ih =>
    intro lam hlam
    have hsplit : alternantPsum m (List.replicate (n + 1) 1) =
        alternantPsum m (List.replicate n 1) * psum (Fin m) ℚ 1 := by
      simp only [alternantPsum, List.replicate_succ', List.map_append, List.prod_append,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    rw [hsplit, cf_mul_psum, card_latticeWords_succ n lam hlam, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_ite, Nat.cast_zero]
    by_cases hgood : 1 ≤ lam i ∧ Antitone (Function.update lam i (lam i - 1))
    · rw [if_pos (by omega), if_pos hgood.1]
      have hup : Function.update (fun j => lam j + stair m j) i (lam i + stair m i - 1) =
          fun j => Function.update lam i (lam i - 1) j + stair m j := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp only [Function.update_self]
          omega
        · simp only [Function.update_of_ne hj]
      rw [hup]
      exact ih _ hgood.2
    · have hR : (if 1 ≤ lam i then
          (((latticeWords n (Function.update lam i (lam i - 1))).card : ℕ) : ℚ) else 0) = 0 := by
        split_ifs with hi
        · rw [latticeWords_eq_empty_of_not_antitone n _ (fun h => hgood ⟨hi, h⟩)]
          simp
        · rfl
      rw [hR]
      split_ifs with hL
      · refine h1 m _ (isAlt_vandermonde_mul_prod _) lam hlam i hL ?_
        by_cases hi : lam i = 0
        · exact Or.inl hi
        · exact Or.inr fun h => hgood ⟨by omega, h⟩
      · rfl

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

namespace CombCfBound

theorem abs_cf_perm {m : ℕ} {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) (σ : Perm (Fin m))
    (v : Fin m → ℕ) : |cf (v ∘ σ.symm) P| = |cf v P| := by
  rw [cf_perm hP σ v, abs_mul]
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]

theorem alternantPsum_cons (m q : ℕ) (ρ : List ℕ) :
    alternantPsum m (q :: ρ) = alternantPsum m ρ * psum (Fin m) ℚ q := by
  unfold alternantPsum
  simp only [List.map_cons, List.prod_cons]
  ring

theorem isAlt_alternantPsum (m : ℕ) (ρ : List ℕ) : IsAlt (alternantPsum m ρ) :=
  isAlt_vandermonde_mul_prod ρ

theorem stair_strictAnti (m : ℕ) : StrictAnti (stair m) := by
  intro i j h
  have hij : (i : ℕ) < j := h
  have := j.isLt
  simp only [stair]
  omega

theorem bound_nil (m : ℕ) (lam : Fin m → ℕ) (hlam : Antitone lam) :
    |cf (fun i => lam i + stair m i) (alternantPsum m [])| ≤ ((latticeWords 0 lam).card : ℚ) := by
  have hA : alternantPsum m [] = alt (stair m) := by
    simp [alternantPsum, vandermondeOf_X_eq_alt]
  have hl : StrictAnti (fun i => lam i + stair m i) := fun i j h =>
    Nat.add_lt_add_of_le_of_lt (hlam h.le) (stair_strictAnti m h)
  rw [hA, cf_alt_of_strictAnti hl (stair_strictAnti m)]
  split_ifs with h
  · have h0 : lam = 0 := by
      funext i
      have := congrFun h i
      show lam i = 0
      omega
    subst h0
    have hne : (latticeWords 0 (0 : Fin m → ℕ)).Nonempty := by
      refine ⟨Fin.elim0, ?_⟩
      simp only [latticeWords, mem_filter, mem_univ, true_and]
      refine ⟨fun t _ i j _ => ?_, fun i => ?_⟩
      · simp [pcnt]
      · simp [pcnt]
    rw [abs_one, Nat.one_le_cast]
    exact Finset.card_pos.mpr hne
  · simp

theorem proof (h1 : CombCfAtStair.Statement) (h2 : CombSortShift.Statement)
    (h3 : CombStripSum.Statement) : CombCfBound.Statement := by
  intro m ρ
  induction ρ with
  | nil => intro _ lam hlam; exact bound_nil m lam hlam
  | cons q ρ ih =>
    intro hpos lam hlam
    have hq : 1 ≤ q := hpos q (by simp)
    have ih' := ih (fun r hr => hpos r (List.mem_cons_of_mem _ hr))
    have hterm : ∀ i : Fin m,
        |(if q ≤ lam i + stair m i then
          cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
            (alternantPsum m ρ) else 0)| ≤
        (if q ≤ lam i + stair m i then
          |cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
            (alternantPsum m (List.replicate ρ.sum 1))| else 0) := by
      intro i
      split_ifs with hqi
      · by_cases hinj :
            Function.Injective (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
        · obtain ⟨σ, μ, hμ, -, hσ⟩ := h2 m lam hlam q i hqi hinj
          have hu : Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q) =
              (fun k => μ k + stair m k) ∘ σ.symm := by
            funext k
            have := hσ (σ.symm k)
            rwa [Equiv.apply_symm_apply] at this
          rw [hu, abs_cf_perm (isAlt_alternantPsum m ρ), abs_cf_perm (isAlt_alternantPsum m _),
            h1 m ρ.sum μ hμ, Nat.abs_cast]
          exact ih' μ hμ
        · simp only [Function.Injective, not_forall] at hinj
          obtain ⟨a, b, hab, hne⟩ := hinj
          rw [cf_eq_zero_of_eq (isAlt_alternantPsum m ρ) hne hab, abs_zero]
          exact abs_nonneg _
      · simp
    rw [alternantPsum_cons, cf_mul_psum]
    calc _ ≤ ∑ i : Fin m, |(if q ≤ lam i + stair m i then
          cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
            (alternantPsum m ρ) else 0)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ => hterm i
      _ ≤ ((latticeWords (ρ.sum + q) lam).card : ℚ) := h3 m ρ.sum q lam hlam hq
      _ = ((latticeWords (q :: ρ).sum lam).card : ℚ) := by rw [List.sum_cons, add_comm]

end CombCfBound

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfMonomialPsumOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Comb

namespace CombCfMonomialPsumOne

theorem sum_update_sub_one {m : ℕ} (l : Fin m → ℕ) (i : Fin m) (h : 1 ≤ l i) :
    ∑ j, Function.update l i (l i - 1) j + 1 = ∑ j, l j := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) l]
  omega

theorem prod_factorial_update_sub_one {m : ℕ} (l v : Fin m → ℕ) (i : Fin m) (hi : v i < l i) :
    (∏ j, ((Function.update l i (l i - 1) j - v j).factorial : ℚ)) * ((l i - v i : ℕ) : ℚ) =
      ∏ j, ((l j - v j).factorial : ℚ) := by
  have hf : (fun j => ((Function.update l i (l i - 1) j - v j).factorial : ℚ)) =
      Function.update (fun j => ((l j - v j).factorial : ℚ)) i ((l i - 1 - v i).factorial : ℚ) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)
      (fun j => ((l j - v j).factorial : ℚ))]
  have h : l i - v i = (l i - 1 - v i) + 1 := by omega
  rw [h, Nat.factorial_succ]
  push_cast
  ring

end CombCfMonomialPsumOne


open CombCfMonomialPsumOne in
theorem CombCfMonomialPsumOne.proof : CombCfMonomialPsumOne.Statement := by
  intro m n v l
  induction n generalizing l with
  | zero =>
    rw [pow_zero, mul_one, cf_monomial]
    by_cases h : l = v
    · subst h; simp
    · rw [if_neg h, if_neg]
      rintro ⟨hle, hs⟩
      apply h
      funext i
      have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => hle i)).1
        (by simpa using hs.symm)
      exact (this i (Finset.mem_univ _)).symm
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, cf_mul_psum]
    simp only [ih]
    by_cases hC : (∀ i, v i ≤ l i) ∧ ∑ i, l i = ∑ i, v i + (n + 1)
    · rw [if_pos hC]
      obtain ⟨hle, hs⟩ := hC
      have hP : (∏ j, ((l j - v j).factorial : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun j _ => by positivity
      rw [Finset.sum_congr rfl (g := fun i => (n.factorial : ℚ) * ((l i - v i : ℕ) : ℚ) /
          ∏ j, ((l j - v j).factorial : ℚ)) ?_]
      · rw [← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum]
        have hsub : ∑ i, (l i - v i) + ∑ i, v i = ∑ i, l i := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i)
        rw [show ∑ i, (l i - v i) = n + 1 by omega, Nat.factorial_succ]
        push_cast
        ring
      · intro i _
        by_cases hi : v i < l i
        · have h1 : 1 ≤ l i := by omega
          have hle' : ∀ j, v j ≤ Function.update l i (l i - 1) j := fun j => by
            by_cases hj : j = i
            · subst hj; simp; omega
            · simp [Function.update_of_ne hj, hle j]
          have hs' := sum_update_sub_one l i h1
          rw [if_pos h1, if_pos ⟨hle', by omega⟩, ← prod_factorial_update_sub_one l v i hi]
          have hne : ((l i - v i : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : l i - v i ≠ 0)
          have hQ : (∏ j, ((Function.update l i (l i - 1) j - v j).factorial : ℚ)) ≠ 0 :=
            Finset.prod_ne_zero_iff.2 fun j _ => by positivity
          field_simp
        · have heq : l i = v i := le_antisymm (not_lt.1 hi) (hle i)
          rw [show ((l i - v i : ℕ) : ℚ) = 0 by rw [heq]; simp, mul_zero, zero_div]
          by_cases h1 : 1 ≤ l i
          · rw [if_pos h1, if_neg]
            rintro ⟨h, _⟩
            have := h i
            simp at this
            omega
          · rw [if_neg h1]
    · rw [if_neg hC]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases h1 : 1 ≤ l i
      · rw [if_pos h1]
        by_cases h2 : (∀ j, v j ≤ Function.update l i (l i - 1) j) ∧
            ∑ j, Function.update l i (l i - 1) j = ∑ j, v j + n
        · exfalso
          apply hC
          obtain ⟨hle', hs'⟩ := h2
          have hle : ∀ j, v j ≤ l j := fun j => (hle' j).trans (by
            by_cases hj : j = i
            · subst hj; simp
            · simp [Function.update_of_ne hj])
          have := sum_update_sub_one l i h1
          exact ⟨hle, by omega⟩
        · rw [if_neg h2]
      · rw [if_neg h1]

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfUpdateZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Comb

theorem CombCfUpdateZero.proof : CombCfUpdateZero.Statement := by
  intro m A hA lam hlam i hpos hcase

  have key : (i : ℕ) + 1 < m ∧ ∀ h : (i : ℕ) + 1 < m, lam ⟨i + 1, h⟩ = lam i := by
    by_cases h0 : lam i = 0
    · have hs : 1 ≤ stair m i := by omega
      simp only [stair] at hs
      refine ⟨by omega, fun h => ?_⟩
      have := hlam (show i ≤ (⟨i + 1, h⟩ : Fin m) from Fin.le_iff_val_le_val.mpr (by simp))
      omega
    · have hna : ¬ Antitone (Function.update lam i (lam i - 1)) := by
        rcases hcase with h | h
        · exact absurd h h0
        · exact h
      have hK : ∃ b : Fin m, i < b ∧ lam i ≤ lam b := by
        by_contra hK
        push Not at hK
        apply hna
        intro a b hab
        simp only [Function.update_apply]
        split_ifs with hb ha ha
        · exact le_rfl
        · have := hlam (show a ≤ i from hb ▸ hab)
          omega
        · have hib : i < b := lt_of_le_of_ne (ha ▸ hab) (fun e => hb e.symm)
          have := hK b hib
          omega
        · exact hlam hab
      obtain ⟨b, hib, hb⟩ := hK
      have hib' : (i : ℕ) < b := hib
      have hm : (i : ℕ) + 1 < m := by have := b.isLt; omega
      refine ⟨hm, fun h => ?_⟩
      have h1 := hlam (show i ≤ (⟨i + 1, h⟩ : Fin m) from Fin.le_iff_val_le_val.mpr (by simp))
      have h2 := hlam (show (⟨i + 1, h⟩ : Fin m) ≤ b from Fin.le_iff_val_le_val.mpr (by simp; omega))
      omega
  obtain ⟨hm, heq⟩ := key
  have hne : i ≠ (⟨i + 1, hm⟩ : Fin m) := by
    intro e
    have := congrArg Fin.val e
    simp at this
  apply cf_eq_zero_of_eq hA hne
  rw [Function.update_self, Function.update_of_ne hne.symm, heq hm]
  simp only [stair] at hpos ⊢
  omega

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfVandermondePsumOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

theorem CombCfVandermondePsumOne.proof (h1 : CombCfMonomialPsumOne.Statement)
    (h2 : CombDetDescFactorial.Statement) : CombCfVandermondePsumOne.Statement := by
  intro m n l hl
  have hA : alternantPsum m (List.replicate n 1) = alt (stair m) * psum (Fin m) ℚ 1 ^ n := by
    simp only [alternantPsum, List.map_replicate, List.prod_replicate, vandermondeOf_X_eq_alt]
  have hterm : ∀ σ : Perm (Fin m),
      cf l (monomial (ex (stair m ∘ σ.symm)) (1 : ℚ) * psum (Fin m) ℚ 1 ^ n) =
        ((n.factorial : ℚ) / ∏ i, ((l i).factorial : ℚ)) *
          ∏ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) := by
    intro σ
    rw [h1]
    have hsum : ∑ i, l i = ∑ i, (stair m ∘ σ.symm) i + n := by
      rw [hl, Function.comp_def, Equiv.sum_comp σ.symm (stair m)]
    by_cases hle : ∀ i, (stair m ∘ σ.symm) i ≤ l i
    · rw [if_pos ⟨hle, hsum⟩]
      have hd : ∀ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) =
          ((l i).factorial : ℚ) / ((l i - stair m (σ.symm i)).factorial : ℚ) := by
        intro i
        rw [eq_div_iff (by positivity), mul_comm]
        exact_mod_cast Nat.factorial_mul_descFactorial (hle i)
      simp only [hd, Finset.prod_div_distrib, Function.comp_apply]
      have hp : (∏ i, ((l i).factorial : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
      have hq : (∏ i, ((l i - stair m (σ.symm i)).factorial : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
      field_simp
    · rw [if_neg (fun h => hle h.1)]
      push Not at hle
      obtain ⟨i, hi⟩ := hle
      simp only [Function.comp_apply] at hi
      have h0 : ∏ j, ((l j).descFactorial (stair m (σ.symm j)) : ℚ) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.descFactorial_eq_zero_iff_lt.mpr hi])
      rw [h0, mul_zero]
  have hdet : ∑ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : ℚ) *
      ∏ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) = vandermondeOf (fun i => (l i : ℚ)) := by
    rw [← h2 m l, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul, ← Equiv.prod_comp σ]
    simp
  rw [hA, alt_eq_sum, Finset.sum_mul, cf_sum]
  simp_rw [smul_mul_assoc, cf_zsmul, hterm]
  calc _ = ((n.factorial : ℚ) / ∏ i, ((l i).factorial : ℚ)) * ∑ σ : Perm (Fin m),
        ((Perm.sign σ : ℤ) : ℚ) * ∏ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [hdet]; ring

end

end GroundTheory.Heights₂.Heights.RestTerms
end

