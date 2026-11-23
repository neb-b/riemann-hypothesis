module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0003

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.DegPolynomialIsHomogeneous
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace RestBoundEq

def lieSign (bot b : Bool) (m : ℕ) : ℚ := if bot = b then (-1) ^ m else -1

theorem lieSign_cases (bot b : Bool) (m : ℕ) : lieSign bot b m = 1 ∨ lieSign bot b m = -1 := by
  unfold lieSign
  split_ifs
  · rcases neg_one_pow_eq_or ℚ m with h | h <;> simp [h]
  · right; rfl

theorem le_dimFl (f j k : ℕ) (hf : 1 ≤ f) : j + k ≤ IndefiniteRowSideFullHecke.RestTerms.dimFl f j k + 1 := by
  unfold IndefiniteRowSideFullHecke.RestTerms.dimFl
  have h1 : (j + k - 1) * 2 ≤ (j + k) * (j + k - 1) := by
    rcases Nat.lt_or_ge (j + k) 2 with h | h
    · have : j + k - 1 = 0 := by omega
      simp [this]
    · rw [mul_comm (j + k)]; exact Nat.mul_le_mul_left _ h
  have h2 : j + k - 1 ≤ (j + k) * (j + k - 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 h1
  have h3 : (j + k) * (j + k - 1) / 2 ≤ f * ((j + k) * (j + k - 1) / 2) :=
    Nat.le_mul_of_pos_left _ hf
  omega

theorem lieClass_reduce (f j k : ℕ) (hf : 1 ≤ f) (bot : Bool)
    (I : IndefiniteRowSideFullHecke.RestTerms.Roots f j k →ₗ[ℝ] ℝ) (hI : IndefiniteRowSideFullHecke.RestTerms.IsFlagIntegral f j k I)
    (Q : Fin f → ℕ → IndefiniteRowSideFullHecke.RestTerms.Roots f j k)
    (hQ : ∀ τ m, 1 ≤ m → m ≤ j + k → (Q τ m).IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k + 1 - m))
    (σ : Fin f × Bool) (τ : Fin f) (m : ℕ) (hm : 2 ≤ m) (hmN : m ≤ j + k) :
    I (IndefiniteRowSideFullHecke.RestTerms.lieClass f j k (m - 1) σ * Q τ m) =
      (lieSign bot σ.2 (m - 1) : ℝ) *
        I (IndefiniteRowSideFullHecke.RestTerms.smallPsum f j k bot (m - 1) σ.1 * Q τ m) := by
  have hD := le_dimFl f j k hf
  have hkill := hI.kills (m - 1) σ.1 (Q τ m) (by omega) (by omega)
    (by convert hQ τ m (by omega) hmN using 1; omega)
  have hsplit : IndefiniteRowSideFullHecke.RestTerms.psumAt f j k (m - 1) σ.1 =
      (∑ a : Fin j, X (σ.1, Fin.castAdd k a) ^ (m - 1)) +
        ∑ b : Fin k, X (σ.1, Fin.natAdd j b) ^ (m - 1) := by
    unfold IndefiniteRowSideFullHecke.RestTerms.psumAt
    exact Fin.sum_univ_add _
  rw [hsplit, add_mul, map_add (f := _)] at hkill
  obtain ⟨τ', b⟩ := σ
  rcases Nat.even_or_odd (m - 1) with he | ho
  · cases bot <;> cases b <;>
      simp [IndefiniteRowSideFullHecke.RestTerms.lieClass, IndefiniteRowSideFullHecke.RestTerms.smallPsum, lieSign, he.neg_pow] <;> linarith
  · cases bot <;> cases b <;>
      simp [IndefiniteRowSideFullHecke.RestTerms.lieClass, IndefiniteRowSideFullHecke.RestTerms.smallPsum, lieSign, ho.neg_pow,
        Finset.sum_neg_distrib, neg_mul, map_neg] <;> linarith

theorem smallPowerSum_isHomogeneous (f r a : ℕ) (c : SmallBlock) (m : ℕ) (τ : Fin f) :
    (smallPowerSum f r a c m τ).IsHomogeneous m := by
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  have h := (isHomogeneous_C_mul_X c.sign (yIndex f r a c τ i)).pow m
  rw [one_mul] at h
  exact h

theorem degPolynomial_isHomogeneous (f r a : ℕ) (c : SmallBlock) :
    (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c).IsHomogeneous
      (topDegree f (r + a)) := by
  have h1 := VandermondeOfHomogeneous.proof
  have hy : ∀ τ i, (yRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_C_mul_X c.sign (yIndex f r a c τ i)
  have hz : ∀ τ i, (zRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_X ℚ (zIndex f r a c τ i)
  have hmu : (smallBlockMu f r a c).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => hy τ i
  have hfib : (fibreClass f r a c).IsHomogeneous
      (∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2)) :=
    IsHomogeneous.prod _ _ _ fun τ _ =>
      (h1 _ ℚ r (yRoot f r a c τ) (hy τ)).mul (h1 _ ℚ a (zRoot f r a c τ) (hz τ))
  have hF := (hmu.pow (f * (r * a))).mul hfib
  have hdeg : 1 * (f * (r * a)) + ∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2) =
      topDegree f (r + a) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, topDegree,
      choose_two_add]
    ring
  rw [← hdeg]
  exact hF

end RestBoundEq

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealEqMulDdConst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

def flagIntegralReal (f N : ℕ) : MvPolynomial (Fin f × Fin N) ℝ →ₗ[ℝ] ℝ where
  toFun G := ∑ α ∈ (blockVandermonde f N).support,
    AddMonoidAlgebra.coeff G α * ((AddMonoidAlgebra.coeff (blockVandermonde f N) α : ℚ) : ℝ) * α.prod (fun _ e => (e.factorial : ℝ))
  map_add' G H := by simp only [MvPolynomial.coeff_add, add_mul, sum_add_distrib]
  map_smul' c G := by simp only [coeff_smul, smul_eq_mul, RingHom.id_apply, mul_sum, mul_assoc]

theorem flagIntegralReal_map (f N : ℕ) (Φ : RootRing f N) :
    flagIntegralReal f N (map (algebraMap ℚ ℝ) Φ) = (flagIntegral f N Φ : ℝ) := by
  simp [flagIntegralReal, flagIntegral, coeff_map, Finsupp.prod]

namespace FlagEq

theorem flagIntegralReal_eq {f N : ℕ} (G : MvPolynomial (Fin f × Fin N) ℝ) :
    flagIntegralReal f N G =
      stairConst f N * ∑ w, ((permSign f N w : ℤ) : ℝ) * AddMonoidAlgebra.coeff G (stairExp f N w) := by
  classical
  have hsub : (blockVandermonde f N).support ⊆
      (blockVandermonde f N).support ∪ univ.image (stairExp f N) := subset_union_left
  show ∑ α ∈ _, _ = _
  rw [sum_subset hsub (fun α _ hα => by rw [notMem_support_iff.mp hα]; simp)]
  have hc : ∀ α : Fin f × Fin N →₀ ℕ, ((AddMonoidAlgebra.coeff (blockVandermonde f N) α : ℚ) : ℝ) =
      ∑ w, ((permSign f N w : ℤ) : ℝ) * if stairExp f N w = α then 1 else 0 := by
    intro α
    rw [coeff_blockVandermonde, Rat.cast_sum]
    refine sum_congr rfl fun w _ => ?_
    split_ifs <;> simp
  simp only [hc, mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  rw [sum_ite_eq, if_pos (mem_union_right _ (mem_image_of_mem _ (mem_univ w))),
    prod_factorial_stairExp]
  ring

theorem ddConst_apply (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G =
      AddMonoidAlgebra.coeff (∑ w : Fin f → Equiv.Perm (Fin (j + k)),
        ((permSign f (j + k) w : ℤ) : ℝ) • rename (Equiv.prodCongrRight w) G) (rho f (j + k)) := by
  simp [IndefiniteRowSideFullHecke.RestTerms.ddConst, IndefiniteRowSideFullHecke.RestTerms.blockAntisym, permSign, rho,
    IndefiniteRowSideFullHecke.RestTerms.rhoMon, coeff_sum, coeff_smul, smul_eq_mul]

theorem ddConst_eq (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G =
      ∑ w, ((permSign f (j + k) w : ℤ) : ℝ) * AddMonoidAlgebra.coeff G (stairExp f (j + k) w) := by
  rw [ddConst_apply, coeff_rho_antisym]

theorem rename_psumAt (f j k m : ℕ) (τ : Fin f) (w : Fin f → Equiv.Perm (Fin (j + k))) :
    rename (Equiv.prodCongrRight w) (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ) =
      IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [IndefiniteRowSideFullHecke.RestTerms.psumAt, map_sum, map_pow, rename_X, Equiv.prodCongrRight_apply]
  exact Equiv.sum_comp (w τ) (fun i => (X (τ, i) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) ^ m)

def antisym (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k :=
  ∑ w : Fin f → Equiv.Perm (Fin (j + k)),
    ((permSign f (j + k) w : ℤ) : ℝ) • rename (Equiv.prodCongrRight w) G

theorem antisym_psumAt_mul (f j k m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    antisym f j k (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) =
      IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * antisym f j k G := by
  simp only [antisym, map_mul, rename_psumAt, mul_sum, mul_smul_comm]

theorem rename_antisym (f j k : ℕ) (u : Fin f → Equiv.Perm (Fin (j + k)))
    (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    rename (Equiv.prodCongrRight u) (antisym f j k G) =
      ((permSign f (j + k) u : ℤ) : ℝ) • antisym f j k G := by
  have hcomp : ∀ w : Fin f → Equiv.Perm (Fin (j + k)),
      rename (Equiv.prodCongrRight u) (rename (Equiv.prodCongrRight w) G) =
        rename (Equiv.prodCongrRight (u * w)) G := by
    intro w
    rw [rename_rename]
    congr 1
  have hs : ((permSign f (j + k) u : ℤ) : ℝ) * ((permSign f (j + k) u : ℤ) : ℝ) = 1 := by
    exact_mod_cast permSign_mul_self u
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [antisym, map_sum, map_smul, hcomp, smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ (fun w => ?_)
  simp only [Equiv.coe_mulLeft, permSign_mul]
  push_cast
  rw [← mul_assoc, hs, one_mul]

theorem coeff_eq_zero_of_swap {f N : ℕ} (A : MvPolynomial (Fin f × Fin N) ℝ)
    (hA : ∀ u : Fin f → Equiv.Perm (Fin N),
      rename (Equiv.prodCongrRight u) A = ((permSign f N u : ℤ) : ℝ) • A)
    (β : Fin f × Fin N →₀ ℕ) (τ : Fin f) (i i' : Fin N) (hii : i ≠ i')
    (hβ : β (τ, i) = β (τ, i')) : AddMonoidAlgebra.coeff A β = 0 := by
  classical
  let u : Fin f → Equiv.Perm (Fin N) := Pi.mulSingle τ (Equiv.swap i i')
  have hu1 : u τ = Equiv.swap i i' := Pi.mulSingle_eq_same _ _
  have hu2 : ∀ τ', τ' ≠ τ → u τ' = 1 := fun τ' h => Pi.mulSingle_eq_of_ne h _
  have hs : permSign f N u = -1 := by
    rw [permSign, Fintype.prod_eq_single τ]
    · rw [hu1, Equiv.Perm.sign_swap hii]; rfl
    · intro τ' h; rw [hu2 τ' h]; simp
  have hfix : (Finsupp.equivFunOnFinite.symm fun v => β (Equiv.prodCongrRight u v)) = β := by
    ext ⟨τ', l⟩
    simp only [Finsupp.coe_equivFunOnFinite_symm, Equiv.prodCongrRight_apply]
    by_cases h : τ' = τ
    · subst h
      rw [hu1]
      rcases eq_or_ne l i with rfl | h1
      · rw [Equiv.swap_apply_left, hβ]
      · rcases eq_or_ne l i' with rfl | h2
        · rw [Equiv.swap_apply_right, hβ]
        · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    · rw [hu2 τ' h]; rfl
  have h := congrArg (AddMonoidAlgebra.coeff · β) (hA u)
  rw [coeff_rename_prodCongrRight, hfix, hs, coeff_smul, smul_eq_mul] at h
  push_cast at h
  linarith

theorem ddConst_psumAt_mul (f j k m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k)
    (hm : 1 ≤ m) : IndefiniteRowSideFullHecke.RestTerms.ddConst f j k (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) = 0 := by
  classical
  rw [ddConst_apply, ← antisym, antisym_psumAt_mul, IndefiniteRowSideFullHecke.RestTerms.psumAt, sum_mul, coeff_sum]
  refine sum_eq_zero fun i _ => ?_
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  split_ifs with h
  · rw [Finsupp.single_le_iff] at h
    simp only [rho, Finsupp.coe_equivFunOnFinite_symm] at h
    have hi : (i : ℕ) + m < j + k := by have := i.isLt; omega
    have hii : i ≠ ⟨(i : ℕ) + m, hi⟩ := by
      intro h'; have := congrArg Fin.val h'; simp at this; omega
    rw [coeff_eq_zero_of_swap _ (fun u => rename_antisym f j k u G) _ τ i ⟨(i : ℕ) + m, hi⟩ hii, mul_zero]
    rw [Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by intro h'; simp at h'; exact hii h'.symm)]
    simp only [rho, Finsupp.coe_equivFunOnFinite_symm]
    omega
  · rfl

theorem ddConst_monomial_rho (f j k : ℕ) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k (monomial (rho f (j + k)) (1 : ℝ)) = 1 := by
  rw [ddConst_eq, Fintype.sum_eq_single 1]
  · simp [stairExp_one, permSign_one]
  · intro w hw
    rw [coeff_monomial, if_neg (fun h => hw (eq_one_of_stairExp_eq w h.symm)), mul_zero]

end FlagEq


open FlagEq in
theorem flagIntegralReal_eq_mul_ddConst (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    flagIntegralReal f (j + k) G = stairConst f (j + k) * IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G := by
  rw [flagIntegralReal_eq, ddConst_eq]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.ImportsAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

noncomputable section

theorem CombTableEqWords.proof (h1 : CombCardYoungCells.Statement)
    (h2 : CombWordOfTableau.Statement) (h3 : CombTableauOfWord.Statement) :
    CombTableEqWords.Statement := by
  intro m lam hlam
  classical
  let e : {T : youngCells lam ≃ Fin (youngCells lam).card // IsStandard T} ≃
      latticeWords (youngCells lam).card lam :=
    { toFun := fun T => ⟨rowWord T.1, (h2 m lam hlam T.1 T.2).1⟩
      invFun := fun w => ⟨Classical.choose (h3 m lam hlam w.1 w.2),
        (Classical.choose_spec (h3 m lam hlam w.1 w.2)).1⟩
      left_inv := by
        rintro ⟨T, hT⟩
        have hs := Classical.choose_spec (h3 m lam hlam (rowWord T) (h2 m lam hlam T hT).1)
        apply Subtype.ext
        have k1 := (h2 m lam hlam _ hs.1).2
        have k2 := (h2 m lam hlam T hT).2
        have hsymm : (Classical.choose
            (h3 m lam hlam (rowWord T) (h2 m lam hlam T hT).1)).symm = T.symm := by
          refine Equiv.ext fun t => Subtype.ext ?_
          rw [← k1 t, ← k2 t, hs.2]
        simpa using congrArg Equiv.symm hsymm
      right_inv := by
        rintro ⟨w, hw⟩
        exact Subtype.ext (Classical.choose_spec (h3 m lam hlam w hw)).2 }
  show Nat.card {T : youngCells lam ≃ Fin (youngCells lam).card // IsStandard T} = _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, h1 m lam]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCharacterAtIdentity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Comb

noncomputable section

theorem symmetricGroupCharacter_eq_cf {m : ℕ} (lam : Fin m → ℕ) (rho : List ℕ) :
    symmetricGroupCharacter lam rho =
      cf (fun i => lam i + stair m i) (alternantPsum m rho) := rfl

theorem CharacterAtIdentity.proof (h1 : CombTableEqWords.Statement)
    (h2 : CombCfAtStair.Statement) : CharacterAtIdentity.Statement := by
  intro m lam hlam
  rw [symmetricGroupCharacter_eq_cf, h2 m (∑ i, lam i) lam hlam, h1 m lam hlam]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCardYoungCells
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem CombCardYoungCells.proof : CombCardYoungCells.Statement := by
  intro m lam
  classical
  unfold youngCells
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hle : lam i ≤ ∑ j, lam j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (lam j)) (Finset.mem_univ i)
  have hset : (Finset.range (∑ j, lam j)).filter (fun c => c < lam i) = Finset.range (lam i) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.card_range (lam i), ← hset, Finset.card_filter]

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCellOfWordInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem Comb.pcnt_lt_of_lt_of_eq {m n : ℕ} (w : Fin n → Fin m) {s t : Fin n} (hst : s < t)
    (i : Fin m) (hs : w s = i) : pcnt w s i < pcnt w t i := by
  unfold pcnt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨s, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      exact ⟨Fin.lt_def.mp hst, hs⟩
    · simp
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact ⟨lt_trans hx.1 (Fin.lt_def.mp hst), hx.2⟩

theorem CombCellOfWordInj.proof : CombCellOfWordInj.Statement := by
  intro m n w s t h
  simp only [cellOfWord, Prod.mk.injEq] at h
  obtain ⟨hw, hc⟩ := h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := Comb.pcnt_lt_of_lt_of_eq w hlt (w s) rfl
    rw [hc, hw] at this
    exact lt_irrefl _ (hw ▸ this)
  · have := Comb.pcnt_lt_of_lt_of_eq w hlt (w t) rfl
    rw [← hc, ← hw] at this
    exact lt_irrefl _ (hw ▸ this)

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCellOfWordMem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem Comb.pcnt_lt_pcnt_of_eq {m n : ℕ} (w : Fin n → Fin m) (t : Fin n) :
    pcnt w t (w t) < pcnt w n (w t) := by
  classical
  unfold pcnt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨t, ?_, ?_⟩
    · simp
    · simp
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact ⟨lt_trans hs.1 t.2, hs.2⟩

theorem CombCellOfWordMem.proof : CombCellOfWordMem.Statement := by
  intro m lam w hw t
  classical
  have hc : ∀ i, pcnt w (youngCells lam).card i = lam i := by
    have := hw
    simp only [latticeWords, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.2
  have hlt : pcnt w t (w t) < lam (w t) := by
    have := Comb.pcnt_lt_pcnt_of_eq w t
    rwa [hc] at this
  have hle : lam (w t) ≤ ∑ i, lam i :=
    Finset.single_le_sum (f := lam) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  simp only [youngCells, cellOfWord, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    Finset.mem_range, true_and]
  exact ⟨lt_of_lt_of_le hlt hle, hlt⟩

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCellOfWordMono
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem Comb.pcnt_succ_self {m n : ℕ} (w : Fin n → Fin m) (t : Fin n) :
    pcnt w ((t : ℕ) + 1) (w t) = pcnt w t (w t) + 1 := by
  unfold pcnt
  have hins : (univ.filter (fun s : Fin n => (s : ℕ) < (t : ℕ) + 1 ∧ w s = w t)) =
      insert t (univ.filter (fun s : Fin n => (s : ℕ) < t ∧ w s = w t)) := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
      · exact Or.inr ⟨h, h2⟩
      · exact Or.inl (Fin.ext h)
    · rintro (h | ⟨h1, h2⟩)
      · subst h; exact ⟨Nat.lt_succ_self _, rfl⟩
      · exact ⟨Nat.lt_succ_of_lt h1, h2⟩
  rw [hins, card_insert_of_notMem]
  simp

theorem CombCellOfWordMono.proof : CombCellOfWordMono.Statement := by
  intro m n w hw s t hrow hcol
  by_contra hst
  rw [not_le] at hst
  simp only [cellOfWord] at hrow hcol
  have h1 : pcnt w ((t : ℕ) + 1) (w t) = pcnt w t (w t) + 1 := Comb.pcnt_succ_self w t
  have h2 : pcnt w ((t : ℕ) + 1) (w s) ≤ pcnt w s (w s) :=
    pcnt_le_of_le w (Nat.succ_le_of_lt hst) (w s)
  have h3 : pcnt w ((t : ℕ) + 1) (w t) ≤ pcnt w ((t : ℕ) + 1) (w s) :=
    hw _ (by have := s.isLt; have : (t : ℕ) < s := hst; omega) (w s) (w t) hrow
  omega

end GroundTheory.Heights₂.Heights.RestTerms
end

