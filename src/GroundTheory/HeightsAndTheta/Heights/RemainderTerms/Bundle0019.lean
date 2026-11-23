module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSameFactorFormula
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombTableauRowCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombTableauRowCount.proof : CombTableauRowCount.Statement := by
  intro m lam T t i
  unfold pcnt rowWord
  apply Finset.card_bij' (fun s _ => T.symm s) (fun p _ => T p)
  · intro s hs
    simp only [mem_filter, mem_univ, true_and, Equiv.apply_symm_apply] at hs ⊢
    exact ⟨hs.2, hs.1⟩
  · intro p hp
    simp only [mem_filter, mem_univ, true_and, Equiv.symm_apply_apply] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  · intro s _
    simp
  · intro p _
    simp

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombTableauRowLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombTableauRowLattice.proof : CombTableauRowLattice.Statement := by
  classical
  intro m lam hlam T hT t i j hij
  have hmem : ∀ p : youngCells lam, p.1.1 = j → (i, p.1.2) ∈ youngCells lam := by
    intro p hp
    have hp' := p.2
    simp only [youngCells, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_range] at hp' ⊢
    have h1 : p.1.2 < lam i := by
      rw [hp] at hp'
      exact lt_of_lt_of_le hp'.2 (hlam hij)
    refine ⟨lt_of_lt_of_le h1 ?_, h1⟩
    exact Finset.single_le_sum (fun k _ => Nat.zero_le (lam k)) (Finset.mem_univ i)
  let f : youngCells lam → youngCells lam := fun p =>
    if h : p.1.1 = j then ⟨(i, p.1.2), hmem p h⟩ else p
  have hf : ∀ p : youngCells lam, ∀ h : p.1.1 = j, f p = ⟨(i, p.1.2), hmem p h⟩ := by
    intro p h
    simp only [f, dif_pos h]
  apply Finset.card_le_card_of_injOn f
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    rw [hf p hp.1]
    refine ⟨rfl, lt_of_le_of_lt ?_ hp.2⟩
    have := hT ⟨(i, p.1.2), hmem p hp.1⟩ p (by simpa [hp.1] using hij) le_rfl
    exact_mod_cast this
  · intro p hp q hq hpq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
    rw [hf p hp.1, hf q hq.1] at hpq
    have h2 : p.1.2 = q.1.2 := by
      have := congrArg (fun x : youngCells lam => x.1.2) hpq
      simpa using this
    apply Subtype.ext
    exact Prod.ext (hp.1.trans hq.1.symm) h2

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombTableauRowPrefix
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombTableauRowPrefix.proof : CombTableauRowPrefix.Statement := by
  intro m lam T hT t
  set c := T.symm t with hc
  have hTc : T c = t := by simp [hc]
  have key : ∀ p : youngCells lam, p.1.1 = c.1.1 →
      ((T p : ℕ) < (t : ℕ) ↔ p.1.2 < c.1.2) := by
    intro p hp
    constructor
    · intro hlt
      by_contra hle'
      have hle := not_lt.mp hle'
      have h := hT c p hp.symm.le hle
      rw [hTc] at h
      exact absurd hlt (not_lt.mpr (Fin.le_def.mp h))
    · intro hlt
      have hle : T p ≤ T c := hT p c hp.le hlt.le
      have hne : p ≠ c := by
        intro h
        rw [h] at hlt
        exact lt_irrefl _ hlt
      have hne' : T p ≠ T c := fun h => hne (T.injective h)
      rw [hTc] at hle hne'
      exact Fin.lt_def.mp (lt_of_le_of_ne hle hne')
  have hcmem : c.1 ∈ youngCells lam := c.2
  simp only [youngCells, mem_filter, mem_product, mem_univ, true_and, mem_range] at hcmem
  rw [show (univ.filter fun p : youngCells lam => p.1.1 = c.1.1 ∧ (T p : ℕ) < (t : ℕ)) =
      univ.filter fun p : youngCells lam => p.1.1 = c.1.1 ∧ p.1.2 < c.1.2 from
    filter_congr fun p _ => and_congr_right (key p)]
  refine Eq.trans ?_ (card_range c.1.2)
  refine card_bij (fun p _ => p.1.2) ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    exact mem_range.mpr hp.2
  · intro p hp q hq hpq
    simp only [mem_filter, mem_univ, true_and] at hp hq
    exact Subtype.ext (Prod.ext (hp.1.trans hq.1.symm) hpq)
  · intro k hk
    rw [mem_range] at hk
    refine ⟨⟨(c.1.1, k), ?_⟩, ?_, rfl⟩
    · simp only [youngCells, mem_filter, mem_product, mem_univ, true_and, mem_range]
      exact ⟨by omega, by omega⟩
    · simp [hk]

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombWordOfTableau
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

theorem CombWordOfTableau.proof (h1 : CombTableauRowCount.Statement)
    (h2 : CombTableauRowPrefix.Statement) (h3 : CombTableauRowLattice.Statement)
    (h4 : CombYoungRowCard.Statement) : CombWordOfTableau.Statement := by
  intro m lam hlam T hT
  refine ⟨?_, fun t => ?_⟩
  · simp only [latticeWords, mem_filter, mem_univ, true_and]
    refine ⟨fun t _ i j hij => ?_, fun i => ?_⟩
    · rw [h1 m lam T t j, h1 m lam T t i]
      exact h3 m lam hlam T hT t i j hij
    · rw [h1 m lam T _ i, ← h4 m lam i]
      congr 1
      exact Finset.filter_congr fun p _ => by simp [(T p).isLt]
  · unfold cellOfWord
    refine Prod.ext rfl ?_
    show pcnt (rowWord T) (t : ℕ) ((T.symm t).1.1) = (T.symm t).1.2
    rw [h1 m lam T t _]
    exact h2 m lam T hT t

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombYoungRowCard
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem CombYoungRowCard.proof : CombYoungRowCard.Statement := by
  intro m lam i
  rw [← Finset.card_range (lam i)]
  refine Finset.card_bij (fun p _ => p.1.2) ?_ ?_ ?_
  · intro p hp
    have hp' : p.1.1 = i := (mem_filter.1 hp).2
    have hc : p.1.2 < lam p.1.1 := (mem_filter.1 p.2).2
    rw [hp'] at hc
    exact mem_range.2 hc
  · intro p hp q hq h
    have hp' : p.1.1 = i := (mem_filter.1 hp).2
    have hq' : q.1.1 = i := (mem_filter.1 hq).2
    exact Subtype.ext (Prod.ext (hp'.trans hq'.symm) h)
  · intro c hc
    have hc' : c < lam i := mem_range.1 hc
    have hmem : ((i, c) : Fin m × ℕ) ∈ youngCells lam := by
      unfold youngCells
      refine mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, mem_range.2 ?_⟩, hc'⟩
      exact lt_of_lt_of_le hc'
        (Finset.single_le_sum (fun j _ => Nat.zero_le (lam j)) (mem_univ i))
    exact ⟨⟨(i, c), hmem⟩, mem_filter.2 ⟨mem_univ _, rfl⟩, rfl⟩

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFrobeniusDimensionFormula
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Comb

theorem FrobeniusDimensionFormula.proof (h1 : CombTableEqWords.Statement)
    (h2 : CombCfAtStair.Statement) (h3 : CombCfVandermondePsumOne.Statement) :
    FrobeniusDimensionFormula.Statement := by
  intro m lam hlam
  have hsum : ∑ i, (lam i + stair m i) = ∑ i, stair m i + ∑ i, lam i := by
    rw [Finset.sum_add_distrib, add_comm]
  have e := h3 m (∑ i, lam i) (fun i => lam i + stair m i) hsum
  rw [h2 m (∑ i, lam i) lam hlam] at e
  rw [h1 m lam hlam, e]
  simp only [stair]

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PLemmaC
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem numStandardTable_eq_frobDim (h1 : FrobeniusDimensionFormula.Statement) {m : ℕ}
    (lam : Fin m → ℕ) (hlam : Antitone lam) :
    (numStandardTable lam : ℚ) = GroundTheory.Heights₂.Heights.frobDim lam := by
  rw [h1 m lam hlam, GroundTheory.Heights₂.Heights.frobDim]
  congr 2
  unfold vandermondeOf
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]

theorem LemmaC.proof (h1 : FrobeniusDimensionFormula.Statement) : LemmaC.Statement := by
  intro r a nu hnu
  have hsum : Antitone (fun i => a + nu i) := fun i j hij => Nat.add_le_add_left (hnu hij) a
  have hrect : Antitone (rectangle r a) := fun _ _ _ => le_rfl
  have hb := GroundTheory.Heights₂.Heights.FrobeniusRectangleBound.intersectionNumber_baseChange r a nu hnu
  rw [← numStandardTable_eq_frobDim h1 _ hsum, ← numStandardTable_eq_frobDim h1 nu hnu,
    show (fun _ : Fin r => a) = rectangle r a from rfl,
    ← numStandardTable_eq_frobDim h1 _ hrect] at hb
  exact_mod_cast hb

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.POtherFactorFormula
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

namespace Top

open MvPolynomial Finset

noncomputable section

theorem isSymmetric_aeval_smul_X {N : ℕ} (s : ℚ) {p : MvPolynomial (Fin N) ℚ} (hp : p.IsSymmetric) :
    (aeval (fun i : Fin N => C s * X i) p).IsSymmetric := by
  intro e
  have key : (rename e).comp (aeval (fun i : Fin N => C s * X i)) =
      (aeval (fun i : Fin N => C s * X i)).comp (rename e) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  have := congrArg (fun φ : MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ p) key
  simp only [AlgHom.comp_apply] at this
  rw [this, hp e]

theorem k_sub_one_le (r a k : ℕ) (hr : 1 ≤ r) (ha : 1 ≤ a) (hk : k ≤ r + a) : k - 1 ≤ r * a := by
  have : r + a ≤ r * a + 1 := by nlinarith
  omega

end

end Top

open _root_.GroundTheory.Heights₂.Heights.RestTerms.Top MvPolynomial Finset

noncomputable section

theorem OtherFactorFormula.proof (hA : LemmaA.Statement) (hB : LemmaB.Statement)
    (hF : FrobeniusCharacterFormula.Statement) (hCI : CharacterAtIdentity.Statement)
    (hV : VandermondeOfHomogeneous.Statement) (hRP : RectangleTablePos.Statement) :
    OtherFactorFormula.Statement := by
  intro f r a c hf hr ha
  obtain ⟨κ, hκpm, hκ⟩ := hasDD_schur hB r a c
  obtain ⟨c0, hc0, hInt, hMain⟩ := hA f (r + a)
  have hκ0 := kappa_ne_zero hκpm
  have hra : r * a ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hfR : (numStandardTable (rectangle r a) : ℚ) ≠ 0 := by exact_mod_cast (hRP r a).ne'
  refine ⟨c0 * κ ^ f, mul_ne_zero hc0 (pow_ne_zero _ hκ0),
    fibreDegree_eq hF hCI hV f r a c hr ha κ hκ c0 hInt, ?_⟩
  intro Q hQ k hk2 hkN τ τ' hττ'
  have hk1 := k_sub_one_le r a k hr ha hkN
  set q : Fin f → ℕ := fun σ => if σ = τ' then k - 1 else 0 with hqdef
  have hGF := smallPowerSum_mul_restPolynomial f r a c k hk2 τ'
  obtain ⟨P, hP, -, S', hS', hI⟩ := hMain _ Q hQ k (by omega) hkN τ _
    (by simpa using isHomogeneous_smallPowerSum f r a c (k - 1) τ')
  have hPeq : P = gmfOut f r a c κ q (f * (r * a) + 1) := by
    apply IsFractionRing.injective (RootRing f (r + a)) (FractionRing (RootRing f (r + a)))
    rw [hP, hGF, dividedDifference_eq_of_hasDD (hasDD_gmf hF f r a c κ hκ q _)]
  have hτ'mem : τ' ∈ Finset.univ.erase τ := Finset.mem_erase.mpr ⟨hττ', Finset.mem_univ τ'⟩
  have hsum : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') = (f - 1) * (r * a) - (k - 1) := by
    rw [← Finset.add_sum_erase _ _ hτ'mem]
    have h2 : ∑ σ' ∈ (Finset.univ.erase τ).erase τ', (r * a - q σ') = (f - 2) * (r * a) := by
      rw [Finset.sum_congr rfl (fun σ hσ => show r * a - q σ = r * a by
        simp [hqdef, Finset.ne_of_mem_erase hσ]), Finset.sum_const,
        Finset.card_erase_of_mem hτ'mem, Finset.card_erase_of_mem (Finset.mem_univ τ),
        Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      congr 1
    rw [h2]
    simp only [hqdef, ite_true]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
    simp only [Nat.add_sub_cancel, show f' + 2 - 1 = f' + 1 by omega]
    rw [add_mul, one_mul]
    omega
  have hle : (f - 1) * (r * a) - (k - 1) ≤ f * (r * a) + 1 :=
    (Nat.sub_le _ _).trans ((Nat.mul_le_mul_right _ (Nat.sub_le f 1)).trans (Nat.le_succ _))
  have hres := restrict_gmfOut f r a c κ q (f * (r * a) + 1) τ
    (fun σ hσ => by simp only [hqdef]; split_ifs <;> omega) (by rw [hsum]; exact hle)
  have hmτ : mstar f r a q (f * (r * a) + 1) τ τ = r * a + k := by
    simp only [mstar, ite_true, hsum]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
    simp only [show f' + 2 - 1 = f' + 1 by omega]
    have h3 : r * a ≤ (f' + 1) * (r * a) := Nat.le_mul_of_pos_left _ (by omega)
    rw [show (f' + 2) * (r * a) = (f' + 1) * (r * a) + r * a by ring]
    omega
  have hms : mstar f r a q (f * (r * a) + 1) τ = fun σ =>
      if σ = τ then r * a + k else if σ = τ' then r * a - (k - 1) else r * a := by
    funext σ
    by_cases hσ : σ = τ
    · subst hσ; rw [hmτ, ite_eq_left rfl]
    · by_cases hσ' : σ = τ'
      · subst hσ'; simp [mstar, hσ, hqdef]
      · simp [mstar, hσ, hσ', hqdef]
  have hqτ : q τ = 0 := by simp [hqdef, Ne.symm hττ']
  rw [hmτ, hqτ, toN_blockOut r a c κ 0 (r * a + k) k (by omega)] at hres
  set χR := symmetricGroupCharacter (rectangle r a) ((k - 1) :: List.replicate (r * a - (k - 1)) 1)
    with hχR
  have hprod : ∏ σ ∈ Finset.univ.erase τ,
      (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ) =
      (χR * κ) * ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 2) := by
    rw [← Finset.mul_prod_erase _ _ hτ'mem]
    congr 1
    · simp only [hqdef, ite_true]
      rw [blockCoeff, ite_eq_right (by omega)]
    · rw [Finset.prod_congr rfl fun σ hσ => by
        rw [show q σ = 0 by simp [hqdef, Finset.ne_of_mem_erase hσ], Nat.sub_zero,
          blockCoeff_rect_eq hCI r a hra]]
      rw [Finset.prod_const, Finset.card_erase_of_mem hτ'mem,
        Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ, Fintype.card_fin]
      congr 1
  have hmult : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) =
      ((f * (r * a) + 1).factorial : ℚ) /
        (((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
          ((r * a).factorial : ℚ) ^ (f - 2)) := by
    have hp : ∏ σ, (mstar f r a q (f * (r * a) + 1) τ σ).factorial =
        (r * a + k).factorial * ((r * a - (k - 1)).factorial * (r * a).factorial ^ (f - 2)) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), hmτ, ← Finset.mul_prod_erase _ _ hτ'mem]
      congr 2
      · simp only [hms, ite_eq_right hττ', ite_true]
      · rw [Finset.prod_congr rfl (fun σ hσ =>
          show (mstar f r a q (f * (r * a) + 1) τ σ).factorial = (r * a).factorial by
            simp only [hms, ite_eq_right (Finset.ne_of_mem_erase hσ),
              ite_eq_right (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hσ))]), Finset.prod_const,
          Finset.card_erase_of_mem hτ'mem, Finset.card_erase_of_mem (Finset.mem_univ τ),
          Finset.card_univ, Fintype.card_fin]
        congr 1
    have hs' := (Finset.mem_piAntidiag.mp
      (mstar_mem f r a q (f * (r * a) + 1) τ (by rw [hsum]; exact hle))).1
    have h := Nat.multinomial_spec (Finset.univ : Finset (Fin f))
      (mstar f r a q (f * (r * a) + 1) τ)
    rw [hp, hs'] at h
    have hden : ((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
        ((r * a).factorial : ℚ) ^ (f - 2) ≠ 0 := by positivity
    rw [eq_div_iff hden, ← h]
    push_cast
    ring
  set T := ∑ nu ∈ partitionsOf r k,
      C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) with hT
  have hTeq : ∑ nu ∈ partitionsOf r k, C (blockCoeff 0 (r * a + k) (fun i => a + nu i)) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) = T := by
    rw [hT]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [blockCoeff, ite_eq_left rfl, ite_eq_right (by omega)]
    have hs := sum_of_mem_partitionsOf hnu
    have hanti := antitone_of_mem_partitionsOf hnu
    have h := hCI r (fun i => a + nu i) (fun i j hij => Nat.add_le_add_left (hanti hij) a)
    have hs2 : ∑ i, (a + nu i) = r * a + k := by
      rw [Finset.sum_add_distrib, hs]
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [hs2] at h
    rw [h]
  rw [hTeq, hprod] at hres
  have hTsym : T.IsSymmetric := by
    intro e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT, map_sum]
    refine Finset.sum_congr rfl fun nu _ => ?_
    rw [map_mul, rename_C, isSymmetric_aeval_smul_X _ (Schur.schur_isSymmetric _) e]
  set K : ℚ := (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) *
    ((χR * κ) * ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 2)) * κ with hK
  have hPS : powerSumHom (r + a) S' = K • T := by
    rw [hS', hPeq, hres, hK, smul_eq_C_mul, smul_eq_C_mul]
    simp only [map_mul, map_pow]
    ring
  have hmultpos : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  by_cases hχ : χR = 0
  · obtain ⟨S, hS⟩ := Flag.exists_powerSumHom_eq hTsym
    have hS'0 : S' = 0 := by
      apply Flag.powerSumHom_injective
      rw [hPS, hK, hχ, map_zero]
      simp
    refine ⟨S, hS, ?_⟩
    rw [restTerm, hI, hS'0, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, hχ]
    ring
  · have hK0 : K ≠ 0 := by
      rw [hK]
      exact mul_ne_zero (mul_ne_zero hmultpos (mul_ne_zero (mul_ne_zero hχ hκ0)
        (pow_ne_zero _ (mul_ne_zero hfR hκ0)))) hκ0
    refine ⟨K⁻¹ • S', ?_, ?_⟩
    · rw [map_smul, hPS, smul_smul, inv_mul_cancel₀ hK0, one_smul]
    · rw [restTerm, hI, coeff_smul, smul_eq_mul]
      rw [hK, hmult]
      have hden : ((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
          ((r * a).factorial : ℚ) ^ (f - 2) ≠ 0 := by positivity
      have hnum : ((f * (r * a) + 1).factorial : ℚ) ≠ 0 := by positivity
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
      simp only [Nat.add_sub_cancel] at hden ⊢
      field_simp
      ring

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

