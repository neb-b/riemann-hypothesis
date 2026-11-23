module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Expand
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.BlockValue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

namespace Top

open MvPolynomial Finset

noncomputable section

def gmf (f r a : ℕ) (c : SmallBlock) (q : Fin f → ℕ) (e : ℕ) : RootRing f (r + a) :=
  (∏ σ, blockEmb f (r + a) σ (yEval r a c (extraFactor r (q σ)))) * smallBlockMu f r a c ^ e *
    fibreClass f r a c

def gmfOut (f r a : ℕ) (c : SmallBlock) (κ : ℚ) (q : Fin f → ℕ) (e : ℕ) : RootRing f (r + a) :=
  ∑ m ∈ Finset.piAntidiag (Finset.univ : Finset (Fin f)) e,
    (Nat.multinomial Finset.univ m : ℚ) •
      ∏ σ, blockEmb f (r + a) σ (blockOut r a c κ (q σ) (m σ))

theorem hasDD_gmf (hF : FrobeniusCharacterFormula.Statement) (f r a : ℕ) (c : SmallBlock) (κ : ℚ)
    (hκ : ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam))
    (q : Fin f → ℕ) (e : ℕ) :
    HasDD f (r + a) (gmf f r a c q e) (gmfOut f r a c κ q e) := by
  rw [gmf, expand_blocks, gmfOut]
  refine hasDD_sum _ fun m _ => hasDD_smul _ (hasDD_prod f (r + a) _ _ fun σ => ?_)
  exact hasDD_block hF r a c κ hκ (q σ) (m σ)

def toN (N : ℕ) : RootRing 1 N →ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
  aeval (fun p : Fin 1 × Fin N => X p.2)

theorem restrictToBlock_blockEmb (f N : ℕ) (τ σ : Fin f) (P : RootRing 1 N) :
    restrictToBlock f N τ (blockEmb f N σ P) =
      if σ = τ then toN N P else C (constantCoeff P) := by
  have key : (restrictToBlock f N τ).comp (blockEmb f N σ) =
      aeval (fun p : Fin 1 × Fin N => if σ = τ then X p.2 else 0) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [restrictToBlock, blockEmb]
  have := congrArg (fun φ : RootRing 1 N →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ P) key
  simp only [AlgHom.comp_apply] at this
  rw [this]
  split_ifs with h
  · rfl
  · rw [show (fun _ : Fin 1 × Fin N => (0 : MvPolynomial (Fin N) ℚ)) = 0 from rfl,
      MvPolynomial.aeval_zero, MvPolynomial.algebraMap_eq]

theorem toN_xSign (r a : ℕ) (c : SmallBlock) (p : MvPolynomial (Fin (r + a)) ℚ) :
    toN (r + a) (xSign r a c p) = aeval (fun i : Fin (r + a) => C c.sign * X i) p := by
  have key : (toN (r + a)).comp (xSign r a c) =
      aeval (fun i : Fin (r + a) => C c.sign * X i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [toN, xSign]
  exact congrArg (fun φ : MvPolynomial (Fin (r + a)) ℚ →ₐ[ℚ] MvPolynomial (Fin (r + a)) ℚ => φ p) key

def mstar (f r a : ℕ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f) : Fin f → ℕ :=
  fun σ => if σ = τ then e - ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') else r * a - q σ

theorem mstar_mem (f r a : ℕ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f)
    (he : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') ≤ e) :
    mstar f r a q e τ ∈ Finset.piAntidiag (Finset.univ : Finset (Fin f)) e := by
  rw [Finset.mem_piAntidiag]
  refine ⟨?_, fun i _ => Finset.mem_univ i⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ τ)]
  have : ∑ x ∈ Finset.univ.erase τ, mstar f r a q e τ x =
      ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') :=
    Finset.sum_congr rfl fun x hx => by simp [mstar, Finset.ne_of_mem_erase hx]
  rw [this]
  simp only [mstar, if_true]
  omega

theorem eq_mstar_of (f r a : ℕ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f) (m : Fin f → ℕ)
    (hm : m ∈ Finset.piAntidiag (Finset.univ : Finset (Fin f)) e)
    (h : ∀ σ, σ ≠ τ → m σ = r * a - q σ) : m = mstar f r a q e τ := by
  funext σ
  by_cases hσ : σ = τ
  · subst hσ
    rw [Finset.mem_piAntidiag] at hm
    have hs := hm.1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ σ)] at hs
    have : ∑ x ∈ Finset.univ.erase σ, m x = ∑ σ' ∈ Finset.univ.erase σ, (r * a - q σ') :=
      Finset.sum_congr rfl fun x hx => h x (Finset.ne_of_mem_erase hx)
    simp only [mstar, if_true]
    omega
  · simp [mstar, hσ, h σ hσ]

theorem restrict_gmfOut (f r a : ℕ) (c : SmallBlock) (κ : ℚ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f)
    (hq : ∀ σ, σ ≠ τ → q σ ≤ r * a)
    (he : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') ≤ e) :
    restrictToBlock f (r + a) τ (gmfOut f r a c κ q e) =
      ((Nat.multinomial Finset.univ (mstar f r a q e τ) : ℚ) *
          ∏ σ ∈ Finset.univ.erase τ, (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ)) •
        toN (r + a) (blockOut r a c κ (q τ) (mstar f r a q e τ τ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [gmfOut, map_sum]
  rw [Finset.sum_eq_single (mstar f r a q e τ)]
  · rw [map_smul, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
    rw [restrictToBlock_blockEmb, if_pos rfl]
    have : ∏ x ∈ Finset.univ.erase τ, restrictToBlock f (r + a) τ
        (blockEmb f (r + a) x (blockOut r a c κ (q x) (mstar f r a q e τ x))) =
        C (∏ σ ∈ Finset.univ.erase τ, (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ)) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun σ hσ => ?_
      have hne := Finset.ne_of_mem_erase hσ
      rw [restrictToBlock_blockEmb, if_neg hne, constantCoeff_blockOut]
      simp only [mstar, if_neg hne]
      rw [if_pos (by have := hq σ hne; omega)]
    rw [this, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_natCast]
    ring
  · intro m hm hne
    obtain ⟨σ, hστ, hσ⟩ : ∃ σ, σ ≠ τ ∧ m σ ≠ r * a - q σ := by
      by_contra hcon
      push Not at hcon
      exact hne (eq_mstar_of f r a q e τ m hm hcon)
    rw [map_smul, map_prod, Finset.prod_eq_zero (Finset.mem_univ σ), smul_zero]
    rw [restrictToBlock_blockEmb, if_neg hστ, constantCoeff_blockOut, if_neg, map_zero]
    have := hq σ hστ
    omega
  · intro h
    exact absurd (mstar_mem f r a q e τ he) h

theorem mem_partitionsOf_iff {m n : ℕ} (lam : Fin m → ℕ) :
    lam ∈ partitionsOf m n ↔ ∑ i, lam i = n ∧ Antitone lam := by
  simp only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
  exact Iff.rfl

theorem toN_blockOut (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m k : ℕ) (hk : q + m = k + r * a) :
    toN (r + a) (blockOut r a c κ q m) =
      C κ * ∑ nu ∈ partitionsOf r k, C (blockCoeff q m (fun i => a + nu i)) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [blockOut, map_sum, Finset.mul_sum]
  have hterm : ∀ lam ∈ partitionsOf r (q + m),
      toN (r + a) (blockCoeff q m lam • pushOut r a c κ lam) =
        if ∀ i, a ≤ lam i then C κ * (C (blockCoeff q m lam) *
          aeval (fun i : Fin (r + a) => C c.sign * X i)
            (schur (Fin (r + a)) (fun i => lam i - a))) else 0 := by
    intro lam _
    rw [map_smul, pushOut]
    split_ifs
    · rw [map_mul, toN_xSign, smul_eq_C_mul]
      simp only [toN, aeval_C, algebraMap_eq]
      ring
    · simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun nu i => a + nu i) (fun lam i => lam i - a) ?_ ?_ ?_ ?_ ?_
  · intro nu hnu
    rw [mem_partitionsOf_iff] at hnu
    rw [Finset.mem_filter, mem_partitionsOf_iff]
    refine ⟨⟨?_, fun i j hij => Nat.add_le_add_left (hnu.2 hij) a⟩, fun i => Nat.le_add_right a _⟩
    rw [Finset.sum_add_distrib, hnu.1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  · intro lam hlam
    rw [Finset.mem_filter, mem_partitionsOf_iff] at hlam
    rw [mem_partitionsOf_iff]
    refine ⟨?_, fun i j hij => Nat.sub_le_sub_right (hlam.1.2 hij) a⟩
    have h1 : ∑ i, (lam i - a) + ∑ i : Fin r, a = ∑ i, lam i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hlam.2 i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    omega
  · intro nu _
    funext i
    simp
  · intro lam hlam
    rw [Finset.mem_filter] at hlam
    funext i
    exact Nat.add_sub_cancel' (hlam.2 i)
  · intro nu _
    simp

theorem blockOut_rect (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m : ℕ) (h : q + m = r * a) :
    blockOut r a c κ q m = C (blockCoeff q m (rectangle r a) * κ) := by
  rw [blockOut, Finset.sum_eq_single (rectangle r a)]
  · have h0 : (fun i : Fin r => rectangle r a i - a) = 0 := funext fun i => by simp [rectangle]
    rw [pushOut, if_pos (fun i => by simp [rectangle]), h0, schur_zero, map_one, mul_one, smul_eq_C_mul,
      ← C_mul, mul_comm]
  · intro lam hlam hne
    rw [pushOut, if_neg, smul_zero]
    intro hall
    apply hne
    rw [mem_partitionsOf_iff] at hlam
    have h1 : ∑ i, (lam i - a) + ∑ i : Fin r, a = ∑ i, lam i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hall i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    have h2 : ∑ i, (lam i - a) = 0 := by omega
    funext i
    have := Finset.sum_eq_zero_iff.mp h2 i (Finset.mem_univ i)
    have := hall i
    simp only [rectangle]
    omega
  · intro h'
    exact absurd ((rectangle_mem_partitionsOf r a _).mpr h) h'

theorem gmfOut_zero (f r a : ℕ) (c : SmallBlock) (κ : ℚ) :
    gmfOut f r a c κ 0 (f * (r * a)) =
      C ((Nat.multinomial Finset.univ (fun _ : Fin f => r * a) : ℚ) *
        (blockCoeff 0 (r * a) (rectangle r a) * κ) ^ f) := by
  rw [gmfOut, Finset.sum_eq_single (fun _ : Fin f => r * a)]
  · simp only [Pi.zero_apply]
    rw [Finset.prod_congr rfl fun σ _ => by rw [blockOut_rect r a c κ 0 (r * a) (by simp)]]
    simp only [blockEmb, rename_C, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [smul_eq_C_mul, ← C_pow, ← C_mul]
  · intro m hm hne
    obtain ⟨σ, hσ⟩ : ∃ σ, m σ < r * a := by
      by_contra hcon
      push Not at hcon
      apply hne
      rw [Finset.mem_piAntidiag] at hm
      have hle : ∀ σ ∈ (Finset.univ : Finset (Fin f)), (fun _ => r * a) σ ≤ m σ :=
        fun σ _ => hcon σ
      have hsum : ∑ σ : Fin f, (fun _ => r * a) σ = ∑ σ, m σ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        rw [hm.1]
      funext σ
      exact ((Finset.sum_eq_sum_iff_of_le hle).mp hsum σ (Finset.mem_univ σ)).symm
    rw [Finset.prod_eq_zero (Finset.mem_univ σ), smul_zero]
    rw [Pi.zero_apply, blockOut_eq_zero_of_lt r a c κ 0 (m σ) (by omega), map_zero]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_piAntidiag]
    refine ⟨by simp, fun i _ => Finset.mem_univ i⟩

end

end Top

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.InhabitantsElem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

theorem flagIntegral_C_mul (f N : ℕ) (b : ℚ) (Φ : RootRing f N) :
    flagIntegral f N (C b * Φ) = b * flagIntegral f N Φ := by
  simp only [flagIntegral, coeff_C_mul, Finset.mul_sum, mul_assoc]

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Lattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms.Comb

open MvPolynomial Finset Equiv

noncomputable section

open scoped Classical

variable {m : ℕ}

def pcnt {n : ℕ} (w : Fin n → Fin m) (t : ℕ) (i : Fin m) : ℕ :=
  (univ.filter (fun s : Fin n => (s : ℕ) < t ∧ w s = i)).card

def IsLattice {n : ℕ} (w : Fin n → Fin m) : Prop :=
  ∀ t ≤ n, ∀ i j : Fin m, i ≤ j → pcnt w t j ≤ pcnt w t i

def latticeWords (n : ℕ) (lam : Fin m → ℕ) : Finset (Fin n → Fin m) :=
  univ.filter (fun w => IsLattice w ∧ ∀ i, pcnt w n i = lam i)

theorem pcnt_castSucc_snoc {n : ℕ} (w : Fin n → Fin m) (a : Fin m) (t : ℕ) (ht : t ≤ n) (i : Fin m) :
    pcnt (Fin.snoc w a : Fin (n + 1) → Fin m) t i = pcnt w t i := by
  unfold pcnt
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
  rw [if_neg (by omega), add_zero]

theorem pcnt_snoc_last {n : ℕ} (w : Fin n → Fin m) (a : Fin m) (i : Fin m) :
    pcnt (Fin.snoc w a : Fin (n + 1) → Fin m) (n + 1) i = pcnt w n i + if a = i then 1 else 0 := by
  unfold pcnt
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    have := s.isLt
    by_cases h : w s = i <;> simp [h, this, Nat.lt_succ_of_lt this]
  · simp

theorem pcnt_zero {n : ℕ} (w : Fin n → Fin m) (i : Fin m) : pcnt w 0 i = 0 := by
  unfold pcnt; simp

theorem pcnt_le_of_le {n : ℕ} (w : Fin n → Fin m) {t t' : ℕ} (h : t ≤ t') (i : Fin m) :
    pcnt w t i ≤ pcnt w t' i := by
  unfold pcnt
  exact Finset.card_le_card (fun s => by simp only [mem_filter, mem_univ, true_and]; omega)

theorem sum_pcnt {n : ℕ} (w : Fin n → Fin m) : ∑ i, pcnt w n i = n := by
  unfold pcnt
  rw [← Finset.card_biUnion]
  · have : (univ : Finset (Fin m)).biUnion (fun i => univ.filter (fun s : Fin n => (s : ℕ) < n ∧ w s = i))
        = univ := by
      ext s; simp
    rw [this, Finset.card_univ, Fintype.card_fin]
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_filter]
    rintro s _ ⟨_, h1⟩ ⟨_, h2⟩
    exact hij (h1 ▸ h2)

theorem update_pred_sub (lam : Fin m → ℕ) (a i : Fin m) (h : 1 ≤ lam a) :
    Function.update lam a (lam a - 1) i + (if a = i then 1 else 0) = lam i := by
  by_cases hai : a = i
  · subst hai; simp; omega
  · simp [Function.update_of_ne (Ne.symm hai), hai]

theorem card_latticeWords_succ (n : ℕ) (lam : Fin m → ℕ) (hlam : Antitone lam) :
    (latticeWords (n + 1) lam).card =
      ∑ a : Fin m, if 1 ≤ lam a then (latticeWords n (Function.update lam a (lam a - 1))).card else 0 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w => w (Fin.last n)) (t := univ)
    (fun _ _ => mem_univ _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · refine Finset.card_nbij' (fun w => Fin.init w) (fun w => Fin.snoc w a) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq, latticeWords, mem_filter, mem_univ, true_and] at hw ⊢
      obtain ⟨⟨hlat, hcont⟩, hlast⟩ := hw
      have hw' : w = Fin.snoc (Fin.init w) a := by
        rw [← hlast]; exact (Fin.snoc_init_self w).symm
      refine ⟨fun t ht i j hij => ?_, fun i => ?_⟩
      · have := hlat t (by omega) i j hij
        rwa [hw', pcnt_castSucc_snoc _ _ _ ht, pcnt_castSucc_snoc _ _ _ ht] at this
      · have := hcont i
        rw [hw', pcnt_snoc_last] at this
        have h2 := update_pred_sub lam a i ha
        omega
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq, latticeWords, mem_filter, mem_univ, true_and] at hw ⊢
      obtain ⟨hlat, hcont⟩ := hw
      refine ⟨⟨fun t ht i j hij => ?_, fun i => ?_⟩, by simp⟩
      · rcases Nat.lt_or_ge t (n + 1) with htn | htn
        · rw [pcnt_castSucc_snoc _ _ _ (by omega), pcnt_castSucc_snoc _ _ _ (by omega)]
          exact hlat t (by omega) i j hij
        · have ht' : t = n + 1 := by omega
          subst ht'
          rw [pcnt_snoc_last, pcnt_snoc_last, hcont, hcont, update_pred_sub lam a i ha,
            update_pred_sub lam a j ha]
          exact hlam hij
      · rw [pcnt_snoc_last, hcont, update_pred_sub lam a i ha]
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq] at hw
      rw [← hw.2]; exact Fin.snoc_init_self w
    · intro w hw
      simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w hw hlast
    simp only [latticeWords, mem_filter, mem_univ, true_and] at hw
    have := hw.2 a
    have h1 : 1 ≤ pcnt w (n + 1) a := by
      unfold pcnt
      exact Finset.card_pos.mpr ⟨Fin.last n, by simp [hlast]⟩
    omega

theorem latticeWords_eq_empty_of_sum_ne (n : ℕ) (lam : Fin m → ℕ) (h : ∑ i, lam i ≠ n) :
    latticeWords n lam = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  simp only [latticeWords, mem_filter, mem_univ, true_and] at hw
  apply h
  rw [← sum_pcnt w]
  exact Finset.sum_congr rfl fun i _ => (hw.2 i).symm

theorem latticeWords_eq_empty_of_not_antitone (n : ℕ) (lam : Fin m → ℕ) (h : ¬ Antitone lam) :
    latticeWords n lam = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  simp only [latticeWords, mem_filter, mem_univ, true_and] at hw
  apply h
  intro i j hij
  rw [← hw.2 i, ← hw.2 j]
  exact hw.1 n le_rfl i j hij

end

end GroundTheory.Heights₂.Heights.RestTerms.Comb
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.NumStandardTablePos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem numStandardTable_pos {m : ℕ} (lam : Fin m → ℕ) : 0 < numStandardTable lam := by
  classical
  let t : Finset (Fin m ×ₗ ℕ) := (youngCells lam).map (toLex : Fin m × ℕ ≃ _).toEmbedding
  have ht : t.card = (youngCells lam).card := Finset.card_map _
  let e : Fin (youngCells lam).card ≃o t := t.orderIsoOfFin ht
  let g : youngCells lam ≃ t :=
    Equiv.subtypeEquiv toLex fun p => by simp [t]
  let T : youngCells lam ≃ Fin (youngCells lam).card := g.trans e.symm.toEquiv
  have hT : ∀ p q : youngCells lam, p.1.1 ≤ q.1.1 → p.1.2 ≤ q.1.2 → T p ≤ T q := by
    intro p q h1 h2
    apply e.symm.monotone
    show toLex p.1 ≤ toLex q.1
    exact Prod.Lex.toLex_mono ⟨h1, h2⟩
  have : Nonempty {T : youngCells lam ≃ Fin (youngCells lam).card //
      ∀ p q : youngCells lam, p.1.1 ≤ q.1.1 → p.1.2 ≤ q.1.2 → T p ≤ T q} := ⟨⟨T, hT⟩⟩
  exact Nat.card_pos

theorem RectangleTablePos.intersectionNumber_baseChange : RectangleTablePos.Statement :=
  fun r a => numStandardTable_pos (rectangle r a)

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAboveTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

theorem CoinvAboveTop.proof (h1 : CoinvPolynomialReduction.Statement)
    (h2 : CoinvIdealComponent.Statement) (h3 : CoinvStaircaseComponent.Statement) :
    CoinvAboveTop.Statement := by
  intro K _ _ f n d H hH hd
  obtain ⟨v, hv, hJ⟩ := h1 K f n H
  obtain ⟨Q, hQ, hcomp⟩ := h2 K f n (H - v) hJ d
  refine ⟨Q, hQ, ?_⟩
  have h0 : homogeneousComponent d v = 0 := (h3 K f n v hv).1 d hd
  have hHd : homogeneousComponent d H = H := by
    rw [homogeneousComponent_of_mem (mem_homogeneousSubmodule d H |>.mpr hH), if_pos rfl]
  rw [← hcomp, map_sub, h0, sub_zero, hHd]

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPolynomialDecomposes
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

theorem RestPolynomialDecomposes.proof (h1 : RestPolynomialHomogeneousDecomposition.Statement) :
    RestPolynomialDecomposes.Statement := by
  intro f r a c
  obtain ⟨Q, hQ, -⟩ := h1 f r a c
  exact ⟨Q, hQ⟩

end GroundTheory.Heights₂.Heights.RestTerms
end

