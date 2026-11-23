module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagSwapDivisible
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

theorem FlagSwapDivisible.dvd_sub_substitute {R σ : Type} [CommRing R] [DecidableEq σ] (a b : σ)
    (Q : MvPolynomial σ R) :
    (X a - X b : MvPolynomial σ R) ∣
      Q - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    rw [map_add (f := _), add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p k hp =>
    rw [map_mul, aeval_X]
    have hk : (X a - X b : MvPolynomial σ R) ∣
        X k - (if k = a then (X b : MvPolynomial σ R) else X k) := by
      split_ifs with h
      · subst h; exact dvd_rfl
      · simp
    have e : p * X k - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p *
          (if k = a then (X b : MvPolynomial σ R) else X k) =
        (p - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p) * X k +
          aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p *
            (X k - (if k = a then (X b : MvPolynomial σ R) else X k)) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hk _)

theorem FlagSwapDivisible.proof : FlagSwapDivisible.Statement := by
  intro σ _ P a b hab hP
  set g : σ → MvPolynomial σ ℚ := fun v => if v = a then X b else X v with hg
  have hswap : g ∘ Equiv.swap a b = g := by
    funext v
    simp only [Function.comp_apply, hg]
    rcases eq_or_ne v a with rfl | hva
    · simp [Equiv.swap_apply_left, hab.symm]
    · rcases eq_or_ne v b with rfl | hvb
      · simp [Equiv.swap_apply_right, hva]
      · simp [Equiv.swap_apply_of_ne_of_ne hva hvb, hva]
  have hzero : aeval g P = 0 := by
    have h1 : aeval g P = -aeval g P := by
      calc aeval g P = aeval (g ∘ Equiv.swap a b) P := by rw [hswap]
        _ = aeval g (rename (Equiv.swap a b) P) := (aeval_rename _ _ _).symm
        _ = -aeval g P := by rw [hP, map_neg]
    have h2 : aeval g P + aeval g P = 0 := by
      nth_rewrite 2 [h1]; exact add_neg_cancel _
    have h3 : (2 : MvPolynomial σ ℚ) * aeval g P = 0 := by rw [two_mul]; exact h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hd := FlagSwapDivisible.dvd_sub_substitute a b P
  rw [← hg, hzero, sub_zero] at hd
  exact hd

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagSymmetricMulAntisym
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagSymmetricMulAntisym.proof : FlagSymmetricMulAntisym.Statement := by
  intro f N P H hP
  unfold antisymmetrize
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [map_mul, hP w, mul_smul_comm]

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagVandermondeDvd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

namespace FlagVandermondeDvd

theorem blockVandermonde_eq_prod (f N : ℕ) :
    blockVandermonde f N =
      ∏ t ∈ (univ : Finset (Fin f × Fin N × Fin N)).filter (fun t => t.2.1 < t.2.2),
        ((X (t.1, t.2.1) - X (t.1, t.2.2) : RootRing f N)) := by
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  simp only [blockVandermonde, vandermondeOf]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have : Finset.Ioi i = (univ : Finset (Fin N)).filter (fun j => i < j) := by ext; simp
  rw [this, Finset.prod_filter]

theorem rename_swap_eq (f N : ℕ) (τ : Fin f) (i j : Fin N) :
    (rename (Equiv.swap (τ, i) (τ, j)) : RootRing f N →ₐ[ℚ] RootRing f N) =
      blockPermute f N (Function.update 1 τ (Equiv.swap i j)) := by
  unfold blockPermute
  congr 1
  funext p
  obtain ⟨σ, k⟩ := p
  by_cases hσ : σ = τ
  · subst hσ
    simp only [Function.update_self, Equiv.swap_apply_def, Prod.mk.injEq, true_and]
    split_ifs <;> rfl
  · simp only [Function.update_of_ne hσ, Pi.one_apply, Equiv.Perm.coe_one, id]
    rw [Equiv.swap_apply_of_ne_of_ne] <;> simp [hσ]

theorem blockSign_update_swap (f N : ℕ) (τ : Fin f) (i j : Fin N) (hij : i ≠ j) :
    blockSign f N (Function.update 1 τ (Equiv.swap i j)) = -1 := by
  unfold blockSign
  rw [Fintype.prod_eq_single τ]
  · simp [Equiv.Perm.sign_swap hij]
  · intro σ hσ
    simp [Function.update_of_ne hσ]

end FlagVandermondeDvd


open FlagVandermondeDvd in
theorem FlagVandermondeDvd.proof (h1 : FlagSwapDivisible.Statement) (h2 : FlagDiffPrime.Statement)
    (h3 : FlagDiffNotDvd.Statement) (h4 : FlagProdPrimesDvd.Statement) :
    FlagVandermondeDvd.Statement := by
  intro f N P hP
  rw [blockVandermonde_eq_prod]
  refine h4 (RootRing f N) (Fin f × Fin N × Fin N) _ _ P ?_ ?_ ?_
  · rintro ⟨τ, i, j⟩ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact h2 _ _ _ (by simp [ht.ne])
  · rintro ⟨τ, i, j⟩ ht ⟨τ', i', j'⟩ ht' hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    refine h3 _ _ _ _ _ (by simp [ht.ne]) (by simp [ht'.ne]) ?_ ?_
    · rintro ⟨ha, hb⟩
      simp only [Prod.mk.injEq] at ha hb
      exact hne (by rw [ha.1, ha.2, hb.2])
    · rintro ⟨ha, hb⟩
      simp only [Prod.mk.injEq] at ha hb
      rw [ha.2, hb.2] at ht
      exact absurd (ht.trans ht') (lt_irrefl _)
  · rintro ⟨τ, i, j⟩ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    refine h1 _ P _ _ (by simp [ht.ne]) ?_
    rw [rename_swap_eq, hP, blockSign_update_swap f N τ i j ht.ne, neg_one_smul]

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagVandermondeHomogeneous
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem FlagVandermondeHomogeneous.proof : FlagVandermondeHomogeneous.Statement := by
  intro f N
  have hblock : ∀ τ : Fin f,
      (vandermondeOf (fun i : Fin N => (X (τ, i) : RootRing f N))).IsHomogeneous
        (N * (N - 1) / 2) := fun τ =>
    VandermondeOfHomogeneous.proof _ _ N _ (fun i => isHomogeneous_X ℚ (τ, i))
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin f))
    (fun τ => vandermondeOf (fun i : Fin N => (X (τ, i) : RootRing f N)))
    (fun _ => N * (N - 1) / 2) (fun τ _ => hblock τ)
  simpa [blockVandermonde, topDegree, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] using h

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFrobeniusCharacterFormula
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem vandermondeOf_X_fin_ne_zero (r : ℕ) :
    vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) ≠ 0 := by
  unfold vandermondeOf
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
  refine sub_ne_zero.mpr fun h => hij ?_
  exact X_injective (R := ℚ) h

theorem vandermondeOf_X_isHomogeneous (r : ℕ) :
    (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ))).IsHomogeneous
      (r * (r - 1) / 2) := by
  have h := IsHomogeneous.prod (σ := Fin r) (R := ℚ) Finset.univ
    (fun i : Fin r => ∏ j ∈ Finset.Ioi i, ((X i : MvPolynomial (Fin r) ℚ) - X j))
    (fun i => ∑ _j ∈ Finset.Ioi i, 1)
    (fun i _ => IsHomogeneous.prod _ _ _ fun j _ =>
      (isHomogeneous_X ℚ i).sub (isHomogeneous_X ℚ j))
  have hdeg : ∑ i : Fin r, ∑ _j ∈ Finset.Ioi i, (1 : ℕ) = r * (r - 1) / 2 := by
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Ioi]
    rw [Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r, ← Finset.sum_range_id]
    exact Finset.sum_range_reflect (fun i => i) r
  rw [hdeg] at h
  exact h

theorem psum_isHomogeneous (σ : Type*) [Fintype σ] (q : ℕ) :
    (psum σ ℚ q).IsHomogeneous q := by
  unfold psum
  exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i q

theorem FrobeniusCharacterFormula.proof (h1 : SchAltPartitionExpansion.Statement) :
    FrobeniusCharacterFormula.Statement := by
  intro r q m _hq
  set V := vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) with hVdef
  set S := psum (Fin r) ℚ q * psum (Fin r) ℚ 1 ^ m with hSdef
  have hprod : ((q :: List.replicate m 1).map fun k => psum (Fin r) ℚ k).prod = S := by
    simp [S, List.map_replicate, List.prod_replicate]
  have halt : Comb.IsAlt (V * S) := by
    have := Comb.isAlt_vandermonde_mul_prod (m := r) (q :: List.replicate m 1)
    rwa [hprod] at this
  have hhom : (V * S).IsHomogeneous (r * (r - 1) / 2 + (q + m)) := by
    have h := (vandermondeOf_X_isHomogeneous r).mul
      ((psum_isHomogeneous (Fin r) q).mul ((psum_isHomogeneous (Fin r) 1).pow m))
    rwa [one_mul] at h
  have hexp := h1 r (q + m) (V * S) halt hhom
  apply mul_left_cancel₀ (vandermondeOf_X_fin_ne_zero r)
  rw [Finset.mul_sum]
  refine hexp.trans (Finset.sum_congr rfl fun lam _ => ?_)
  simp only [symmetricGroupCharacter, hprod]
  ring

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHookTableauCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem vandermondeOf_succ {R : Type*} [CommRing R] {n : ℕ} (v : Fin (n + 1) → R) :
    vandermondeOf v =
      (∏ j : Fin n, (v 0 - v j.succ)) * vandermondeOf (fun j : Fin n => v j.succ) := by
  have key : ∀ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (v i - v j) =
      ∏ j : Fin (n + 1), if i < j then v i - v j else 1 := by
    intro i
    rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]
  unfold vandermondeOf
  simp only [key]
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp [Fin.succ_pos]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_succ]
    simp only [Fin.succ_lt_succ_iff, Fin.not_lt_zero, if_false, one_mul]
    rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]

theorem numStandardTable_zero (m : ℕ) : numStandardTable (fun _ : Fin m => (0 : ℕ)) = 1 := by
  have hc : youngCells (fun _ : Fin m => (0 : ℕ)) = ∅ := by
    ext c
    simp [youngCells]
  have : IsEmpty (youngCells (fun _ : Fin m => (0 : ℕ))) :=
    ⟨fun p => by simpa [hc] using p.2⟩
  have : IsEmpty (Fin (youngCells (fun _ : Fin m => (0 : ℕ))).card) := by
    rw [hc]
    exact Fin.isEmpty'
  unfold numStandardTable
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext (Equiv.ext fun p => isEmptyElim p)⟩,
    ⟨⟨Equiv.equivOfIsEmpty _ _, fun p => isEmptyElim p⟩⟩⟩

theorem prod_range_sub_eq_descFactorial (n l : ℕ) :
    ∏ j ∈ Finset.range l, (n - j) = n.descFactorial l := by
  induction l with
  | zero => simp
  | succ l ih => rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ, mul_comm]

theorem prod_fin_sub_eq_factorial (l : ℕ) : ∏ j : Fin l, (l - (j : ℕ)) = l.factorial := by
  rw [Fin.prod_univ_eq_prod_range (fun j => l - j) l,
    ← Finset.prod_range_reflect (fun j => l - j) l]
  have : ∀ j ∈ Finset.range l, l - (l - 1 - j) = j + 1 := by
    intro j hj
    have := Finset.mem_range.1 hj
    omega
  rw [Finset.prod_congr rfl this, Finset.prod_range_add_one_eq_factorial]

theorem vandermondeOf_add_const {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) (c : R) :
    vandermondeOf (fun j => v j + c) = vandermondeOf v := by
  unfold vandermondeOf
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  ring

theorem numStandardTable_hookShape_succ (h : FrobeniusDimensionFormula.Statement) {k l : ℕ}
    (hlk : l < k) : numStandardTable (hookShape (l + 1) k l) = Nat.choose (k - 1) l := by
  have hanti : Antitone (hookShape (l + 1) k l) := by
    intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    unfold hookShape
    split_ifs <;> omega
  have e0 : hookShape (l + 1) k l 0 + (l + 1 - 1 - ((0 : Fin (l + 1)) : ℕ)) = k := by
    simp [hookShape]
    omega
  have es : ∀ j : Fin l, hookShape (l + 1) k l j.succ + (l + 1 - 1 - ((j.succ : Fin (l + 1)) : ℕ)) =
      (0 + (l - 1 - (j : ℕ))) + 1 := by
    intro j
    have := j.isLt
    unfold hookShape
    rw [Fin.val_succ, if_neg (by omega), if_pos (by omega)]
    omega
  have hsum : ∑ i, hookShape (l + 1) k l i = k := by
    rw [Fin.sum_univ_succ]
    have hs1 : ∀ j : Fin l, hookShape (l + 1) k l j.succ = 1 := fun j => by
      have h1 := es j
      have h2 := j.isLt
      have h3 : ((j.succ : Fin (l + 1)) : ℕ) = j + 1 := Fin.val_succ j
      omega
    simp only [hs1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    have := e0
    have hval : ((0 : Fin (l + 1)) : ℕ) = 0 := rfl
    omega
  have hf := h (l + 1) (hookShape (l + 1) k l) hanti
  simp only [vandermondeOf_succ, Fin.prod_univ_succ] at hf
  rw [e0, hsum] at hf
  simp only [es] at hf
  have hz := h l (fun _ => 0) antitone_const
  beta_reduce at hz
  rw [numStandardTable_zero] at hz
  simp only [Finset.sum_const_zero, Nat.factorial_zero, Nat.cast_one, one_mul] at hz
  set V := vandermondeOf (fun j : Fin l => ((0 + (l - 1 - (j : ℕ)) : ℕ) : ℚ)) with hV
  set P := ∏ j : Fin l, ((0 + (l - 1 - (j : ℕ))).factorial : ℚ) with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => by positivity
  have hVP : V = P := by
    field_simp at hz
    exact hz.symm
  have hshift : vandermondeOf (fun j : Fin l => (((0 + (l - 1 - (j : ℕ))) + 1 : ℕ) : ℚ)) = V := by
    rw [hV, ← vandermondeOf_add_const (fun j : Fin l => ((0 + (l - 1 - (j : ℕ)) : ℕ) : ℚ)) 1]
    congr 1
    funext j
    push_cast
    ring
  have hnum : ∏ j : Fin l, ((k : ℚ) - (((0 + (l - 1 - (j : ℕ))) + 1 : ℕ) : ℚ)) =
      ((k - 1).descFactorial l : ℚ) := by
    rw [← prod_range_sub_eq_descFactorial, Nat.cast_prod,
      ← Finset.prod_range_reflect (fun j => ((k - 1 - j : ℕ) : ℚ)) l,
      ← Fin.prod_univ_eq_prod_range (fun j => ((k - 1 - (l - 1 - j) : ℕ) : ℚ)) l]
    refine Finset.prod_congr rfl fun j _ => ?_
    have := j.isLt
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hden : ∏ j : Fin l, (((0 + (l - 1 - (j : ℕ))) + 1 : ℕ).factorial : ℚ) =
      (l.factorial : ℚ) * P := by
    rw [hP, ← prod_fin_sub_eq_factorial, Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have := j.isLt
    rw [Nat.factorial_succ, Nat.cast_mul]
    congr 2
    omega
  rw [hnum, hshift, hden, hVP, Nat.descFactorial_eq_factorial_mul_choose] at hf
  have hk0 : ((k.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have hl0 : ((l.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have : (numStandardTable (hookShape (l + 1) k l) : ℚ) = ((k - 1).choose l : ℚ) := by
    rw [hf]
    push_cast
    field_simp
  exact_mod_cast this

theorem HookTableauCount.proof (h : FrobeniusDimensionFormula.Statement) :
    HookTableauCount.Statement := by
  intro r k l hlk hlr
  rw [← YoungDiagramCombinatorics.numSYT_hookShape r k l hlr, YoungDiagramCombinatorics.numSYT_hookShape (l + 1) k l (by omega)]
  exact numStandardTable_hookShape_succ h hlk

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PLemmaA
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem LemmaA.proof (h1 : FlagIntegralTopDegree.Statement)
    (h2 : FlagIntegralVandermondePos.Statement) (h3 : FlagDividedDifferencePoly.Statement)
    (h4 : FlagAntisymDecomposition.Statement) (h5 : FlagVandermondeHomogeneous.Statement)
    (h6 : FlagAntisymHomogeneous.Statement) (h7 : FlagQuotientHomogeneous.Statement)
    (h8 : FlagRestrictHomogeneous.Statement) (h9 : FlagRestrictSymmetric.Statement)
    (h10 : FlagRestrictDecomposition.Statement) (h11 : FlagPowerSumPreimage.Statement)
    (h12 : FlagRestrictConstantCoeff.Statement) (h13 : FlagIntegralViaQuotient.Statement) :
    LemmaA.Statement := by
  intro f N
  refine ⟨flagIntegral f N (blockVandermonde f N) / (N.factorial : ℚ) ^ f, ?_, ?_, ?_⟩
  · exact div_ne_zero (h2 f N).ne' (pow_ne_zero _ (Nat.cast_ne_zero.mpr N.factorial_ne_zero))
  · exact fun H hH => h1 f N H hH
  intro F Q hF k hk1 hkN τ G hG
  choose R hR hRsym using fun l σ => h3 f N (G * Q l σ)
  set P : RootRing f N := ∑ l ∈ Finset.Icc 1 N, ∑ σ : Fin f, blockPowerSum f N l σ * R l σ
    with hPdef
  have hanti : antisymmetrize f N (G * F) = blockVandermonde f N * P := h4 f N F G Q R hF hR
  refine ⟨P, ?_, ?_, ?_⟩
  · have hΔ : algebraMap (RootRing f N) (FractionRing (RootRing f N)) (blockVandermonde f N) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (RootRing f N) _)).mpr
        (Flag.blockVandermonde_ne_zero f N)
    rw [dividedDifference, hanti, map_mul, mul_div_cancel_left₀ _ hΔ]
  · intro hFh
    have hGF : (G * F).IsHomogeneous (topDegree f N + k) := by
      have := hG.mul hFh
      rwa [show k - 1 + (topDegree f N + 1) = topDegree f N + k by omega] at this
    have hA := h6 f N (G * F) _ hGF
    rw [hanti] at hA
    exact h8 f N τ P k (h7 _ _ _ _ _ (Flag.blockVandermonde_ne_zero f N) (h5 f N) hA)
  · obtain ⟨S, hS, hScoeff⟩ := h11 N (fun l => restrictToBlock f N τ (R l τ))
      (fun l => h9 f N τ (R l τ) (hRsym l τ))
    refine ⟨S, ?_, ?_⟩
    · rw [hS, hPdef, h10]
    · rw [hScoeff k hk1 hkN, h12, h13 f N _ _ (hR k τ)]

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

