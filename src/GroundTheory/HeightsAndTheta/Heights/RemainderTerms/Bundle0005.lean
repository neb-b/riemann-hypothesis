module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStepReduction
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

open Coinv

theorem CoinvStepReduction.proof : CoinvStepReduction.Statement := by
  classical
  intro K _ _ f n b k e he
  obtain ⟨c, hc⟩ := Coinv.exists_reduction (K := K) (f := f) (n := n) b k
  set φ : ↥(Finset.Ioi k) → Fin f × Fin n := fun s => (b, (s : Fin n)) with hφ
  have hinj : Function.Injective φ := fun s t h => Subtype.ext (Prod.ext_iff.mp h).2
  obtain ⟨e₀, rfl⟩ : ∃ e₀ : Fin f × Fin n →₀ ℕ, e = e₀ + Finsupp.single (b, k) ((k : ℕ) + 1) := by
    refine ⟨e - Finsupp.single (b, k) ((k : ℕ) + 1), ?_⟩
    ext u
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    by_cases hu : u = (b, k)
    · subst hu; simp only [Finsupp.single_eq_same]; omega
    · simp [Ne.symm hu]
  set P : MvPolynomial (Fin f × Fin n) K := ∑ j ∈ range ((k : ℕ) + 1),
      monomial e₀ 1 * (rename φ (-c j) * X (b, k) ^ j) with hP
  refine ⟨P.support, fun e' => P.coeff e', ?_, ?_⟩
  · intro e' he'
    have h1 := support_sum he'
    rw [Finset.mem_biUnion] at h1
    obtain ⟨j, hj, hj'⟩ := h1
    have h2 := support_mul _ _ hj'
    rw [Finset.mem_add] at h2
    obtain ⟨a, ha, d', hd', rfl⟩ := h2
    have ha' : a = e₀ := Finset.mem_singleton.mp (support_monomial_subset ha)
    have h3 := support_mul _ _ hd'
    rw [Finset.mem_add] at h3
    obtain ⟨d, hd, s, hs, rfl⟩ := h3
    rw [X_pow_eq_monomial] at hs
    have hs' : s = Finsupp.single (b, k) j := Finset.mem_singleton.mp (support_monomial_subset hs)
    rw [support_rename_of_injective hinj, Finset.mem_image] at hd
    obtain ⟨d₀, -, rfl⟩ := hd
    subst ha' hs'
    have hoff : ∀ u : Fin f × Fin n, (u.1 ≠ b ∨ u.2 ≤ k) → Finsupp.mapDomain φ d₀ u = 0 := by
      intro u hu
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨s, rfl⟩
      have hks : k < (s : Fin n) := Finset.mem_Ioi.mp s.2
      rcases hu with hu | hu
      · exact hu rfl
      · exact absurd hu (not_le.mpr hks)
    rw [Finset.mem_range] at hj
    refine ⟨fun u hu => ?_, ?_⟩
    · have hne : u ≠ (b, k) := by
        rintro rfl
        rcases hu with h | ⟨-, h⟩ <;> exact lt_irrefl _ h
      have h0 := hoff u (by
        rcases hu with h | ⟨-, h⟩
        · exact Or.inl (ne_of_lt h)
        · exact Or.inr (le_of_lt h))
      simp [h0, Ne.symm hne]
    · have h0 := hoff (b, k) (Or.inr le_rfl)
      simp only [Finsupp.add_apply, h0, Finsupp.single_eq_same]
      omega
  · have hsum : ∑ e' ∈ P.support, P.coeff e' • monomial e' (1 : K) = P := by
      conv_rhs => rw [P.as_sum]
      refine Finset.sum_congr rfl fun e' _ => ?_
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hsum]
    have hm : monomial (e₀ + Finsupp.single (b, k) ((k : ℕ) + 1)) (1 : K) =
        monomial e₀ 1 * X (b, k) ^ ((k : ℕ) + 1) := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    have hdiff : monomial (e₀ + Finsupp.single (b, k) ((k : ℕ) + 1)) (1 : K) - P =
        monomial e₀ 1 * (X (b, k) ^ ((k : ℕ) + 1) +
          ∑ j ∈ range ((k : ℕ) + 1), rename φ (c j) * X (b, k) ^ j) := by
      rw [hm, hP, mul_add, Finset.mul_sum]
      simp only [map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
    rw [hdiff]
    exact Ideal.mul_mem_left _ _ hc

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHookSumBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem exists_hookShape_of_isHook {r k : ℕ} (hk : 1 ≤ k) (nu : Fin r → ℕ) (hanti : Antitone nu)
    (hsum : ∑ i, nu i = k) (hhook : ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) :
    ∃ l, l < r ∧ l < k ∧ nu = hookShape r k l := by
  set g : ℕ → ℕ := fun j => if h : j < r then nu ⟨j, h⟩ else 0 with hg
  have hgnu : ∀ i : Fin r, g i = nu i := fun i => by simp [hg, i.isLt]
  have hsumg : ∑ j ∈ range r, g j = k := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [hgnu]
    exact hsum
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      simp at hsumg
      omega
    · exact h
  have hanti_g : ∀ i j, i ≤ j → g j ≤ g i := by
    intro i j hij
    by_cases hj : j < r
    · have hi : i < r := lt_of_le_of_lt hij hj
      simp only [hg, dif_pos hj, dif_pos hi]
      exact hanti (show (⟨i, hi⟩ : Fin r) ≤ ⟨j, hj⟩ from hij)
    · simp [hg, dif_neg hj]
  have hle1 : ∀ j, 1 ≤ j → g j ≤ 1 := by
    intro j hj
    by_cases h : j < r
    · simp only [hg, dif_pos h]
      exact hhook ⟨j, h⟩ (by simp only; omega)
    · simp [hg, dif_neg h]
  have hsplit : g 0 + ∑ j ∈ Ico 1 r, g j = k := by
    rw [← Finset.sum_eq_sum_Ico_succ_bot hr, ← Finset.range_eq_Ico]
    exact hsumg
  set t := ∑ j ∈ Ico 1 r, g j with ht
  have hrow : ∀ i, 1 ≤ i → i < r → g i = if i ≤ t then 1 else 0 := by
    intro i hi1 hir
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hle1 i hi1) with h0 | h1
    · have hz : ∀ j ∈ Ico i r, g j = 0 := fun j hj => by
        have := hanti_g i j (mem_Ico.mp hj).1
        omega
      have hti : t ≤ i - 1 := by
        rw [ht, ← Finset.sum_Ico_consecutive g hi1 hir.le, Finset.sum_eq_zero hz, add_zero]
        calc ∑ j ∈ Ico 1 i, g j ≤ ∑ j ∈ Ico 1 i, 1 :=
              Finset.sum_le_sum fun j hj => hle1 j (mem_Ico.mp hj).1
          _ = i - 1 := by simp
      rw [h0, if_neg (by omega)]
    · have ho : ∀ j ∈ Ico 1 (i + 1), g j = 1 := fun j hj => by
        have h2 := hanti_g j i (by have := (mem_Ico.mp hj).2; omega)
        have h3 := hle1 j (mem_Ico.mp hj).1
        omega
      have hit : i ≤ t := by
        rw [ht, ← Finset.sum_Ico_consecutive g (show 1 ≤ i + 1 by omega)
          (show i + 1 ≤ r by omega), Finset.sum_congr rfl ho]
        simp
      rw [h1, if_pos hit]
  have htr : t < r := by
    have : t ≤ r - 1 := by
      calc t ≤ ∑ j ∈ Ico 1 r, 1 := Finset.sum_le_sum fun j hj => hle1 j (mem_Ico.mp hj).1
        _ = r - 1 := by simp
    omega
  have hg0 : 1 ≤ g 0 := by
    by_contra h
    have hz : ∀ j, g j = 0 := fun j => by
      have := hanti_g 0 j (Nat.zero_le j)
      omega
    simp [hz] at hsumg
    omega
  refine ⟨t, htr, by omega, ?_⟩
  funext i
  rw [← hgnu i]
  unfold hookShape
  by_cases hi0 : (i : ℕ) = 0
  · rw [if_pos hi0, hi0]
    omega
  · rw [if_neg hi0, hrow i (by omega) i.isLt]

theorem HookSumBound.proof (hC : LemmaC.Statement) (hH : HookTableauCount.Statement) :
    HookSumBound.Statement := by
  intro r a k b hk hb
  have hB0 : (0 : ℚ) ≤ (Nat.choose (r * a + k) k : ℚ) * numStandardTable (rectangle r a) := by
    positivity
  have hterm : ∀ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
      |b nu| ≤ ((Nat.choose (r * a + k) k : ℚ) * numStandardTable (rectangle r a)) *
        (numStandardTable nu : ℚ) := by
    intro nu hnu
    have hmem := (Finset.mem_filter.mp hnu).1
    have h := Finset.mem_filter.mp hmem
    have hsum : ∑ i, nu i = k := Finset.Nat.mem_antidiagonalTuple.mp h.1
    have hc := hC r a nu (fun i j hij => h.2 i j hij)
    rw [hsum] at hc
    calc |b nu| ≤ numStandardTable (fun i => a + nu i) := hb nu hmem
      _ ≤ _ := by exact_mod_cast hc
  have himg : (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) ⊆
      (range (min r k)).image (hookShape r k) := by
    intro nu hnu
    obtain ⟨hmem, hhook⟩ := Finset.mem_filter.mp hnu
    have h := Finset.mem_filter.mp hmem
    obtain ⟨l, hlr, hlk, rfl⟩ := exists_hookShape_of_isHook hk nu (fun i j hij => h.2 i j hij)
      (Finset.Nat.mem_antidiagonalTuple.mp h.1) hhook
    exact Finset.mem_image.mpr ⟨l, Finset.mem_range.mpr (lt_min hlr hlk), rfl⟩
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hhooks : ∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
      (numStandardTable nu : ℚ) ≤ 2 ^ (k - 1) := by
    calc _ ≤ ∑ nu ∈ (range (min r k)).image (hookShape r k), (numStandardTable nu : ℚ) :=
          Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => by positivity
      _ ≤ ∑ l ∈ range (min r k), (numStandardTable (hookShape r k l) : ℚ) :=
          Finset.sum_image_le_of_nonneg fun _ _ => by positivity
      _ = ∑ l ∈ range (min r k), ((k - 1).choose l : ℚ) := by
          refine Finset.sum_congr rfl fun l hl => ?_
          have hl' := lt_min_iff.mp (Finset.mem_range.mp hl)
          rw [hH r k l hl'.2 hl'.1]
      _ ≤ ∑ l ∈ range k, ((k - 1).choose l : ℚ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_right _ _))
            fun _ _ _ => by positivity
      _ = 2 ^ (k - 1) := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          rw [Nat.add_sub_cancel]
          exact_mod_cast Nat.sum_range_choose n
  calc _ ≤ ((Nat.choose (r * a + k) k : ℚ) * numStandardTable (rectangle r a)) * 2 ^ (k - 1) :=
        mul_le_mul_of_nonneg_left hhooks hB0
    _ = _ := by ring

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.POtherFactorBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem OtherFactorBound.add_le_mul_add_one {r a : ℕ} (hr : 1 ≤ r) (ha : 1 ≤ a) :
    r + a ≤ r * a + 1 := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  nlinarith [Nat.zero_le (r' * a')]

theorem OtherFactorBound.coeff_bound (hS : SchurSignCoefficient.Statement)
    (hH : HookSumBound.Statement) (r a k : ℕ) (c : SmallBlock) (hk1 : 1 ≤ k) (hkN : k ≤ r + a)
    (S : MvPolynomial (Fin (r + a)) ℚ)
    (hSeq : powerSumHom (r + a) S =
      ∑ nu ∈ partitionsOf r k,
        C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) *
          aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu)) :
    |S.coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1)| ≤
      (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) * numStandardTable (rectangle r a) / k := by
  set e := Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1 with he
  have hs : c.sign = 1 ∨ c.sign = -1 := by cases c <;> simp [SmallBlock.sign]
  have hex : ∀ nu : Fin r → ℕ, ∃ T : MvPolynomial (Fin (r + a)) ℚ, nu ∈ partitionsOf r k →
      powerSumHom (r + a) T = aeval (fun i : Fin (r + a) => C c.sign * X i)
          (schur (Fin (r + a)) nu) ∧
        AddMonoidAlgebra.coeff T e = c.sign ^ k * if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          (-1 : ℚ) ^ ((Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card) / k
        else 0 := by
    intro nu
    by_cases hnu : nu ∈ partitionsOf r k
    · have hmem := hnu
      simp only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hmem
      obtain ⟨T, hT1, hT2⟩ := hS (r + a) r k hk1 hkN nu c.sign hs
        (fun i j hij => hmem.2 i j hij) hmem.1
      exact ⟨T, fun _ => ⟨hT1, hT2⟩⟩
    · exact ⟨0, fun h => absurd h hnu⟩
  choose T hT using hex
  have hSsum : S = ∑ nu ∈ partitionsOf r k,
      C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * T nu := by
    apply Flag.powerSumHom_injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hSeq, map_sum]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [map_mul, (hT nu hnu).1]
    congr 1
    simp [powerSumHom]
  have hterm : ∀ nu ∈ partitionsOf r k,
      |((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * (T nu).coeff e| =
        (if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) else 0) / k := by
    intro nu hnu
    rw [(hT nu hnu).2, abs_mul, abs_mul, abs_pow]
    have habs : |c.sign| = 1 := by rcases hs with h | h <;> simp [h]
    rw [habs, one_pow, one_mul, Nat.abs_cast]
    split_ifs
    · rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]; ring
    · simp
  calc |S.coeff e|
      = |∑ nu ∈ partitionsOf r k,
          ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * (T nu).coeff e| := by
        rw [hSsum, coeff_sum]
        simp only [coeff_C_mul]
    _ ≤ ∑ nu ∈ partitionsOf r k,
          |((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * (T nu).coeff e| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = (∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
          |((numStandardTable (fun i => a + nu i) : ℕ) : ℚ)|) / k := by
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_filter]
        simp only [Nat.abs_cast]
    _ ≤ (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) * numStandardTable (rectangle r a) / k := by
        gcongr
        exact hH r a k (fun nu => ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ)) hk1
          (fun nu _ => by simp)

theorem OtherFactorBound.proof (hO : OtherFactorFormula.Statement)
    (hF : SameFactorFormula.Statement) (hS : SchurSignCoefficient.Statement)
    (hB : CharacterBound.Statement) (hH : HookSumBound.Statement)
    (hR : RectangleTablePos.Statement) (hD : RestPolynomialDecomposes.Statement) :
    OtherFactorBound.Statement := by
  intro f r a c hf hr ha
  have hP : (0 : ℚ) < numStandardTable (rectangle r a) := by exact_mod_cast hR r a
  have hkey := OtherFactorBound.add_le_mul_add_one hr ha
  refine ⟨?_, hD f r a c, ?_⟩
  · obtain ⟨C₀, hC₀, hJ, -⟩ := hF f r a c hf hr ha
    rw [hJ]
    have h1 : ((f * (r * a)).factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((r * a).factorial : ℚ) ≠ 0 := by positivity
    have := hP.ne'
    simp_all
  intro Q hQ k hk2 hkN τ τ' hne
  have hk1 : k - 1 ≤ r * a := by omega
  refine ⟨fun h => absurd h (by omega), ?_⟩
  have hf2 : 2 ≤ f := by
    by_contra h
    have : f = 1 := by omega
    subst this
    exact hne (Subsingleton.elim _ _)
  obtain ⟨C₀, hC₀, hJ, hT⟩ := hO f r a c hf2 hr ha
  obtain ⟨S, hSeq, hTk⟩ := hT Q hQ k hk2 hkN τ τ' hne
  have hcoef := OtherFactorBound.coeff_bound hS hH r a k c (by omega) hkN S hSeq
  have hchi := hB r (rectangle r a) ((k - 1) :: List.replicate (r * a - (k - 1)) 1)
    (fun _ _ _ => le_rfl) (by
      intro q hq
      simp only [List.mem_cons, List.mem_replicate] at hq
      omega)
  rw [hTk, hJ]
  set y := AddMonoidAlgebra.coeff S (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1)
  set z := symmetricGroupCharacter (rectangle r a) ((k - 1) :: List.replicate (r * a - (k - 1)) 1)
  set P : ℚ := (numStandardTable (rectangle r a) : ℚ) with hPdef
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
  have hg : g + 2 - 2 = g := by omega
  rw [hg]

  set n1 := r * a with hn1
  set n := (g + 2) * n1 with hn
  have hD1 : ((n1 + k).factorial : ℚ) =
      (Nat.choose (n1 + k) k : ℚ) * (k.factorial : ℚ) * (n1.factorial : ℚ) := by
    have := Nat.add_choose_mul_factorial_mul_factorial n1 k
    rw [← this]; push_cast; ring
  have hA : (n1.factorial : ℚ) =
      ((n1 - (k - 1)).factorial : ℚ) * (n1.descFactorial (k - 1) : ℚ) := by
    exact_mod_cast (Nat.factorial_mul_descFactorial hk1).symm
  have hM : ((n + 1).factorial : ℚ) = ((n + 1 : ℕ) : ℚ) * (n.factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hdesc : (0 : ℚ) < n1.descFactorial (k - 1) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hk1
  have hchoose : (0 : ℚ) < Nat.choose (n1 + k) k := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hBpos : (0 : ℚ) < (n1 - (k - 1)).factorial := by positivity
  have hKpos : (0 : ℚ) < k.factorial := by positivity
  have hnpos : (0 : ℚ) < n.factorial := by positivity
  have hkpos : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)

  have hstep : |C₀ * k * ((n + 1).factorial : ℚ) /
        (((n1 + k).factorial : ℚ) * ((n1 - (k - 1)).factorial : ℚ) *
          ((n1).factorial : ℚ) ^ g) * P ^ g * z * y| ≤
      ((n + 1 : ℕ) : ℚ) * |C₀ * (n.factorial : ℚ) / ((n1).factorial : ℚ) ^ (g + 2) * P ^ (g + 2)| *
        ((n1.descFactorial (k - 1) : ℚ) * 2 ^ (k - 1)) / (k.factorial : ℚ) := by
    rw [hD1, hM]
    have hApos : (0 : ℚ) < n1.factorial := by positivity
    simp only [abs_mul, abs_div, abs_pow, Nat.abs_cast, abs_of_pos hP]
    have hX1 : 0 ≤ |C₀| * (k : ℚ) * (((n + 1 : ℕ) : ℚ) * (n.factorial : ℚ)) /
        ((Nat.choose (n1 + k) k : ℚ) * (k.factorial : ℚ) * (n1.factorial : ℚ) *
          ((n1 - (k - 1)).factorial : ℚ) * (n1.factorial : ℚ) ^ g) * P ^ g := by positivity
    refine (mul_le_mul (mul_le_mul_of_nonneg_left hchi hX1) hcoef (abs_nonneg _)
      (by positivity)).trans (le_of_eq ?_)
    field_simp
    rw [hA]
    ring
  refine hstep.trans ?_

  have hX : (n1.descFactorial (k - 1) : ℚ) * 2 ^ (k - 1) ≤ restX r a ^ (k - 1) := by
    have h1 : (n1.descFactorial (k - 1) : ℚ) ≤ (n1 : ℚ) ^ (k - 1) := by
      exact_mod_cast Nat.descFactorial_le_pow n1 (k - 1)
    have h2 : (2 * (n1 : ℚ)) ≤ restX r a := by
      simp only [restX, hn1]; push_cast; nlinarith [(Nat.cast_nonneg (r + a : ℕ) : (0 : ℚ) ≤ _)]
    calc (n1.descFactorial (k - 1) : ℚ) * 2 ^ (k - 1)
        ≤ (n1 : ℚ) ^ (k - 1) * 2 ^ (k - 1) := by gcongr
      _ = (2 * (n1 : ℚ)) ^ (k - 1) := by ring
      _ ≤ restX r a ^ (k - 1) := by gcongr
  have hpos1 : 0 ≤ ((n + 1 : ℕ) : ℚ) := by positivity
  gcongr

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem RestBound.proof (h₁ : RestPrimeBound.Statement) (h₂ : RestBoundOfPrimeBound.Statement) :
    RestBound.Statement := by
  intro f r a c B₀ hf hr ha hB
  refine ⟨(h₁ f r a c B₀ hf hr ha hB).1, ?_⟩
  intro Q hQ s e he P
  exact h₂ f r a c B₀ hf hr ha hB Q s e
    (fun p hp hpB => (h₁ f r a c B₀ hf hr ha hB).2 Q hQ s e he p hp hpB) P

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestInnerTsumBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem RestInnerTsumBound.proof : RestInnerTsumBound.Statement := by
  intro p k c M hp hk hc
  obtain ⟨hsum, hle⟩ := GeometricTail.intersectionNumber_baseChange p k hp hk
  have hM : 0 ≤ M := (abs_nonneg (c 0)).trans (hc 0)
  have hnn : ∀ n : ℕ, 0 ≤ (p ^ ((n + 1) * k))⁻¹ := fun n => by
    have : (0 : ℝ) ≤ p := by linarith
    positivity
  have hbound : ∀ n : ℕ, ‖(p ^ ((n + 1) * k))⁻¹ * c n‖ ≤ (p ^ ((n + 1) * k))⁻¹ * M := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn n)]
    exact mul_le_mul_of_nonneg_left (hc n) (hnn n)
  have hsumM : Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * M) := hsum.mul_right M
  have hS : Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * c n) :=
    Summable.of_norm_bounded hsumM hbound
  refine ⟨hS, ?_⟩
  calc |∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * c n|
      = ‖∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * c n‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖(p ^ ((n + 1) * k))⁻¹ * c n‖ := norm_tsum_le_tsum_norm hS.norm
    _ ≤ ∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * M := hS.norm.tsum_le_tsum hbound hsumM
    _ = (∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹) * M := tsum_mul_right
    _ ≤ (2 * (p ^ k)⁻¹) * M := mul_le_mul_of_nonneg_right hle hM
    _ = M * (2 * (p ^ k)⁻¹) := mul_comm _ _

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPolynomialHomogeneousDecomposition
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem RestPolynomialHomogeneousDecomposition.proof (h1 : CoinvAboveTop.Statement)
    (h2 : RestPolynomialHomogeneous.Statement) :
    RestPolynomialHomogeneousDecomposition.Statement := by
  intro f r a c
  obtain ⟨Q, hQ, hF⟩ := h1 ℚ f (r + a) (topDegree f (r + a) + 1) (restPolynomial f r a c)
    (h2 f r a c) (by unfold Coinv.coinvTop topDegree; omega)
  exact ⟨Q, hF, hQ⟩

end GroundTheory.Heights₂.Heights.RestTerms
end

