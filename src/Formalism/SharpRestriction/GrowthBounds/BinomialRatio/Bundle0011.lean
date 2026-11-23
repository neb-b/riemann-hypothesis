module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0010
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeAlternative
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TopDegreeLeTwoB
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.LeAndHalfLeProdOneSubExpNegOfBounds
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeRatioConsecutive
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairCount
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgePlane

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.AiAddMulLeA0
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem coarse_ratio_small {Al Ai Pl Pi bl bi b' be k p : ℝ} (hAl : 0 ≤ Al) (hb : 0 < b') (_hbe0 : 0 ≤ be) (hbe : be ≤ 1 / 12)
    (hPi : 0 < Pi) (hp : 0 < p) (hP : p * Pi ≤ Pl) (h1 : Al * Pl ≤ bl) (h2 : bl ≤ b' * (1 + be))
    (h3 : bi - k * Pi < Ai * Pi) (h4 : b' * (1 - be) ≤ bi) : Al ≤ 2 * (Ai + k) / p := by
  rw [le_div_iff₀ hp]
  have e1 : Al * (p * Pi) ≤ Al * Pl := mul_le_mul_of_nonneg_left hP hAl
  have e2 : b' * be ≤ b' * (1 / 12) := mul_le_mul_of_nonneg_left hbe hb.le
  have e3 : Al * p * Pi ≤ 2 * (Ai + k) * Pi := by nlinarith
  exact le_of_mul_le_mul_right e3 hPi

theorem Ai_add_mul_le_A0 {Ai A0 de ε k p N1 La s : ℝ} (hAi : 0 ≤ Ai) (hA : Ai * (1 + de) < A0) (hde : 40 * ε ≤ de)
    (hde6 : de < 1 / 6) (hε : ε = N1 * La / k) (hk : 5 ≤ k) (hkA : k ≤ A0) (hp : k ^ 2 ≤ p) (hLa : 1 ≤ La)
    (hN1 : 1 ≤ N1) (_hs0 : 0 ≤ s) (hs : s ≤ N1) :
    Ai + s * (2 * (Ai + k) / p + 2 * La * A0 / k) ≤ A0 := by
  have hk0 : 0 < k := by linarith
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hA0 : 0 < A0 := by linarith
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hde0 : 0 ≤ de := by linarith
  have hAiA : Ai ≤ A0 := by nlinarith

  have h1 : A0 * de < (A0 - Ai) * (1 + de) := by nlinarith
  have h2 : (A0 - Ai) * (1 + de) ≤ (A0 - Ai) * (7 / 6) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 : A0 * (40 * ε) ≤ A0 * de := mul_le_mul_of_nonneg_left hde hA0.le
  have h4 : 34 * (ε * A0) ≤ A0 - Ai := by nlinarith

  have c1 : 2 * (Ai + k) / p ≤ 4 * A0 / k ^ 2 := by
    rw [div_le_div_iff₀ hp0 (by positivity)]
    have : 2 * (Ai + k) ≤ 4 * A0 := by linarith
    calc 2 * (Ai + k) * k ^ 2 ≤ 4 * A0 * k ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ 4 * A0 * p := mul_le_mul_of_nonneg_left hp (by positivity)
  have c2 : 4 * A0 / k ^ 2 ≤ La * A0 / k := by
    rw [div_le_div_iff₀ (by positivity) hk0]
    have : 4 * A0 * k ≤ La * A0 * k * k := by
      have : 4 * A0 ≤ La * A0 * k := by nlinarith [mul_le_mul hLa hk (by norm_num) (by linarith)]
      nlinarith
    nlinarith
  have c3 : 2 * (Ai + k) / p + 2 * La * A0 / k ≤ 3 * (La * A0 / k) := by
    have : 2 * La * A0 / k = 2 * (La * A0 / k) := by ring
    linarith
  have c30 : 0 ≤ La * A0 / k := by positivity
  have c4 : s * (2 * (Ai + k) / p + 2 * La * A0 / k) ≤ N1 * (3 * (La * A0 / k)) :=
    mul_le_mul hs c3 (by positivity) (by linarith)
  have c5 : N1 * (3 * (La * A0 / k)) = 3 * (ε * A0) := by rw [hε]; ring
  have c6 : 0 ≤ ε * A0 := by positivity
  linarith

variable {C0 Cde CE1 CE2 H : ℝ} {X : Loc}

theorem partial_width_le_cap [NeZero X.m] (hH : 1 ≤ H) (h : Std C0 Cde CE1 CE2 H X) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (hK : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b)
    (i : Fin (segS X.TT j)) (hi : i.val < (X.seg C0 CE1 CE2 j).sigma) (n : ℕ) (hn : n ≤ i.val + 1) :
    (∑ l : Fin (segS X.TT j), if l.val < i.val + 1 then (b.w l : ℤ) else 0) ≤ cap X.p (X.seg C0 CE1 CE2 j) b n := by
  obtain ⟨hd, -, hSt, -⟩ := hK
  set S := X.seg C0 CE1 CE2 j with hS

  have hk5 := h.k5
  have hk0 : 0 < X.k := by linarith
  have hp0 : (0 : ℝ) < X.p := by linarith [h.p1]
  have hde : 40 * eps X C0 ≤ X.de C0 Cde := by
    have := h.LaK
    unfold eps
    calc 40 * (X.N1 * X.La C0 / X.k) = 40 * X.N1 * X.La C0 / X.k := by ring
      _ ≤ _ := this
  have hbe12 : be X C0 ≤ 1 / 12 := by
    have h1 := h.beLe
    have h2 := h.de6
    have h3 : 0 ≤ 18 * X.N1 * X.La C0 / X.k := by
      have := h.La1
      positivity
    linarith
  have hA0k : X.k ≤ (S.A0 X.p : ℝ) := by
    refine le_trans ?_ (h.half_ratio_le_segment_base_of_std j)
    have hQ0 : 0 < X.Q := by linarith [h.Q1]
    rw [le_div_iff₀ (by positivity)]
    have h1 := h.kQ hH
    have h2 := h.ba
    have h3 : X.k * (2 * X.Q) ≤ X.k ^ 3 * X.Q := by
      have hk2 : (2 : ℝ) ≤ X.k ^ 2 := by nlinarith
      calc X.k * (2 * X.Q) = (X.k * X.Q) * 2 := by ring
        _ ≤ (X.k * X.Q) * X.k ^ 2 := mul_le_mul_of_nonneg_left hk2 (mul_pos hk0 hQ0).le
        _ = X.k ^ 3 * X.Q := by ring
    linarith
  have hcb : ∀ l : Fin (segS X.TT j),
      (coarseA X.p S b l : ℝ) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get l) : ℕ) : ℝ) ≤ X.bT (segPos X.TT j l) ∧
      (X.bT (segPos X.TT j l) : ℝ) - ((X.m : ℝ) + 1) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get l) : ℕ) : ℝ) <
        (coarseA X.p S b l : ℝ) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get l) : ℕ) : ℝ) := fun l =>
    coarse_bounds (X.bT (segPos X.TT j l)) (X.p ^ (segG X.TT j - (segDists X.TT j).get l)) (b.rz l)
      (fun c => (hd.1 l c).1) (hd.2.1 l).1 (hd.2.1 l).2
  have hAi := (coarse_degree_alternative hH h j b hd i).1 hi
  set c1 : ℝ := 2 * ((coarseA X.p S b i : ℝ) + X.k) / X.p with hc1
  set c2 : ℝ := 2 * X.La C0 * (S.A0 X.p : ℝ) / X.k with hc2
  have hc10 : 0 ≤ c1 := by rw [hc1]; positivity
  have hc20 : 0 ≤ c2 := by
    have := h.La1
    have : (0 : ℝ) ≤ (S.A0 X.p : ℝ) := by linarith
    rw [hc2]; positivity
  have hterm : ∀ l : Fin (segS X.TT j),
      ((if l.val < i.val + 1 then ((coarseA X.p S b l : ℤ) + (b.sg l : ℤ)) else 0 : ℤ) : ℝ) ≤
        (if l = i then (coarseA X.p S b i : ℝ) else 0) + (c1 + c2) := by
    intro l
    by_cases hl : l.val < i.val + 1
    · rw [if_pos hl]
      have hlσ : l.val < S.sigma := by omega
      have hsg : (b.sg l : ℝ) ≤ c2 := (hSt l hlσ).2.2.2.2
      push_cast
      by_cases hli : l = i
      · rw [if_pos hli, hli]
        rw [hli] at hsg
        linarith
      · rw [if_neg hli]
        have hlt : l < i := by
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hl) with h' | h'
          · exact h'
          · exact absurd (Fin.ext h') hli
        have hdl := dist_strictMono X.TT j hlt
        have hdi := (dist_pos_lt X.TT j i).2
        have hPP : X.p * X.p ^ (segG X.TT j - (segDists X.TT j).get i) ≤
            X.p ^ (segG X.TT j - (segDists X.TT j).get l) := by
          rw [← pow_succ']
          exact Nat.pow_le_pow_right (by have := h.p5; omega) (by omega)
        have hPP' : (X.p : ℝ) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) ≤
            ((X.p ^ (segG X.TT j - (segDists X.TT j).get l) : ℕ) : ℝ) := by exact_mod_cast hPP
        have := coarse_ratio_small (k := X.k) (Nat.cast_nonneg _) h.bpos h.be0 hbe12 (h.levels j i).1 hp0 hPP' (hcb l).1
          (h.winB _ (pos_mem X.TT j l).1).2 (hcb i).2 (h.winB _ (pos_mem X.TT j i).1).1
        linarith
    · rw [if_neg hl]
      push_cast
      split_ifs
      · have : (0 : ℝ) ≤ (coarseA X.p S b i : ℝ) := Nat.cast_nonneg _
        linarith
      · linarith
  have hsumR : ((∑ l : Fin (segS X.TT j),
      (if l.val < i.val + 1 then ((coarseA X.p S b l : ℤ) + (b.sg l : ℤ)) else 0) : ℤ) : ℝ) ≤ (S.A0 X.p : ℝ) := by
    rw [Int.cast_sum]
    refine le_trans (Finset.sum_le_sum fun l _ => hterm l) ?_
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsN : ((segS X.TT j : ℕ) : ℝ) ≤ X.N1 := by exact_mod_cast (h.segB j).2
    have hpk : X.k ^ 2 ≤ (X.p : ℝ) := by
      have h1 := h.pk
      have h2 := h.Y1
      have : X.k ^ 2 * 1 ≤ X.k ^ 2 * X.Y ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      linarith
    exact Ai_add_mul_le_A0 (ε := eps X C0) (Nat.cast_nonneg _) hAi hde h.de6 rfl hk5 hA0k hpk h.La1 h.one_le_level_alt (Nat.cast_nonneg _) hsN
  have hsumZ : (∑ l : Fin (segS X.TT j),
      (if l.val < i.val + 1 then ((coarseA X.p S b l : ℤ) + (b.sg l : ℤ)) else 0)) ≤ S.A0 X.p := by
    exact_mod_cast hsumR

  unfold cap
  have hcmp : ∀ l : Fin (segS X.TT j),
      (if l.val < i.val + 1 then (b.w l : ℤ) else 0) ≤
        (if l.val < i.val + 1 then ((coarseA X.p S b l : ℤ) + (b.sg l : ℤ)) else 0) * 0 +
        ((if (l : ℕ) < n then ((coarseA X.p S b l : ℤ) - (oEff S b l : ℤ)) else 0) +
          (if l.val < i.val + 1 then ((coarseA X.p S b l : ℤ) + (b.sg l : ℤ)) else 0)) := by
    intro l
    by_cases hl : l.val < i.val + 1
    · have hlσ : l.val < S.sigma := by omega
      have hw : (b.w l : ℤ) ≤ (coarseA X.p S b l : ℤ) := by exact_mod_cast (hSt l hlσ).2.1
      have hsg0 : (0 : ℤ) ≤ (b.sg l : ℤ) := Int.natCast_nonneg _
      have ho : (oEff S b l : ℤ) = (b.w l : ℤ) + (b.sg l : ℤ) := by
        unfold oEff
        rw [if_pos hlσ]
        push_cast
        ring
      rw [if_pos hl, if_pos hl]
      split_ifs
      · rw [ho]; linarith
      · linarith
    · have hln : ¬ (l : ℕ) < n := by omega
      rw [if_neg hl, if_neg hl, if_neg hln]
      simp
  have hs := Finset.sum_le_sum (s := Finset.univ) fun l _ => hcmp l
  simp only [mul_zero, zero_add] at hs
  rw [Finset.sum_add_distrib] at hs
  linarith

theorem top_rows_bound_holds : LeadingRowsBeyondThreshold :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 => by
      intro X _ hD hI hc j b hK i hi
      have hs := std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc
      exact ⟨partial_width_le_cap le_rfl hs j b hK i hi i.val (by omega), partial_width_le_cap le_rfl hs j b hK i hi (i.val + 1) le_rfl⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreesLargeBeyond
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def PairFactsAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) →
        ∀ (mu : Fin (2 * segS X.TT j + 1 + 1) → Fin (X.m + 1) → ℤ) (lam : Fin X.m → ℤ),
          IsPair A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
          pairC mu 0 = (A : ℤ) ∧ (∀ l, 0 ≤ pairC mu l) ∧
          (∀ i : Fin (segS X.TT j), 0 ≤ pairRho mu i ∧ pairRho mu i ≤ pairC mu i ∧
            ((pairRho mu i : ℤ) : ℝ) ≤ (clA C0 CE1 CE2 X j rz ry i : ℝ) * (1 + 4 / (X.p : ℝ) ^ 2) ∧
            -(4 * (clA C0 CE1 CE2 X j rz ry i : ℝ) / (X.p : ℝ) ^ 2) ≤
              ((pairO mu (clA C0 CE1 CE2 X j rz ry) i - pairRho mu i : ℤ) : ℝ)) ∧
          0 ≤ lam 0 ∧ lam 0 ≤ pairC mu (segS X.TT j) ∧
          ∀ i : Fin (segS X.TT j), 0 ≤ pairN (s := segS X.TT j) lam i ∧
            ((pairN (s := segS X.TT j) lam i : ℤ) : ℝ) ≤ (clC C0 CE1 CE2 X j rz ry i : ℝ) * (1 + 4 / (X.p : ℝ) ^ 2)

def CoarseDegreesLargeAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        X.k ^ 3 ≤ (A : ℝ) ∧ (∀ i, X.k ^ 3 ≤ (clA C0 CE1 CE2 X j rz ry i : ℝ)) ∧
          (∀ i, X.k ^ 3 ≤ (clC C0 CE1 CE2 X j rz ry i : ℝ)) ∧ X.k ^ 2 ≤ (X.p : ℝ) ∧ 10 ≤ X.k ∧
          1 ≤ X.La C0 ∧ 4 * X.La C0 ≤ X.k

def RestPairFacts : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => PairFactsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc
def CoarseDegreesLargeBeyond : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => CoarseDegreesLargeAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairFacts
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Finset

theorem pf_tele (L K : ℕ → ℤ) (q : ℕ) (h : ∀ t, t < q → L (t + 1) ≤ K t) :
    ∑ t ∈ range (q + 1), (L t - K t) ≤ L 0 - K q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [sum_range_succ]
    have h1 := ih fun t ht => h t (by omega)
    have h2 := h q (by omega)
    linarith

def pfMass {r : ℕ} (v : Fin r → ℤ) : ℤ := ∑ t, max 0 (-(v t))

theorem pfMass_up {r : ℕ} {nu mu : Fin r → ℤ} {g : ℕ} (h : Strip nu mu g) : pfMass nu ≤ pfMass mu :=
  Finset.sum_le_sum fun t _ => max_le_max le_rfl (neg_le_neg (h.1 t))

theorem pfMass_down {r : ℕ} {nu mu : Fin r → ℤ} {g : ℕ} (h : Strip nu mu g) : pfMass mu ≤ pfMass nu + g := by
  have e : ∀ t, max 0 (-(mu t)) ≤ max 0 (-(nu t)) + (nu t - mu t) := fun t => by
    have := h.1 t
    rcases le_total 0 (-(mu t)) with h1 | h1 <;> rcases le_total 0 (-(nu t)) with h2 | h2 <;>
      simp only [max_eq_left, max_eq_right, h1, h2] <;> omega
  calc pfMass mu ≤ ∑ t, (max 0 (-(nu t)) + (nu t - mu t)) := Finset.sum_le_sum fun t _ => e t
    _ = pfMass nu + g := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h.2.2]; rfl

variable {s r : ℕ} {A : ℕ} {Ai Ci : Fin s → ℕ} {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ} {lam : Fin r → ℤ}

theorem pf_mass (h : IsChain (kLetters A Ai Ci) mu) : ∀ (n : ℕ) (hn : n ≤ s),
    pfMass (fun t : Fin r => mu ⟨2 * n + 1, by omega⟩ t.succ) ≤ ∑ x : Fin s, if x.val < n then (Ci x : ℤ) else 0 := by
  intro n
  induction n with
  | zero =>
    intro _
    have e : (⟨2 * 0 + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = 1 := rfl
    rw [e]
    unfold pfMass
    simp [chain_first_tail (N := 2 * s) h (by simp [kLetters])]
  | succ n ih =>
    intro hn
    have h0 := ih (by omega)
    obtain ⟨hW, hC, -, -, -, -, -, -⟩ := pair_top h (⟨n, by omega⟩ : Fin s)
    have h1 := pfMass_up hW
    have h2 := pfMass_down hC
    have h3 := sum_lt_succ (fun x : Fin s => (Ci x : ℤ)) (⟨n, by omega⟩ : Fin s)
    simp only at h3
    rw [h3]
    have e : (⟨2 * (n + 1) + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = ⟨2 * n + 3, by omega⟩ := Fin.ext (by show 2 * (n + 1) + 1 = 2 * n + 3; omega)
    rw [e]
    have h4 : ((Ci ⟨n, by omega⟩ - (pairSg mu Ai ⟨n, by omega⟩).toNat : ℕ) : ℤ) ≤ (Ci ⟨n, by omega⟩ : ℤ) := by
      exact_mod_cast Nat.sub_le _ _
    linarith

theorem pf_prev_le [NeZero r] (h : IsChain (kLetters A Ai Ci) mu) : ∀ (n : ℕ) (hn : n ≤ s),
    mu ⟨2 * n + 1, by omega⟩ (0 : Fin r).succ ≤ ∑ x : Fin s, if x.val < n then pairW mu x.val else 0 := by
  intro n
  induction n with
  | zero =>
    intro _
    have e : (⟨2 * 0 + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = 1 := rfl
    rw [e, chain_first_tail (N := 2 * s) h (by simp [kLetters])]
    exact (Finset.sum_eq_zero fun x _ => if_neg (Nat.not_lt_zero _)).symm.le
  | succ n ih =>
    intro hn
    have h0 := ih (by omega)
    obtain ⟨hW, hC, hw, -, -, -, -, -⟩ := pair_top h (⟨n, by omega⟩ : Fin s)
    have h1 := strip_first hW
    have h2 := hC.1 (0 : Fin r)
    have h3 := sum_lt_succ (fun x : Fin s => pairW mu x.val) (⟨n, by omega⟩ : Fin s)
    simp only at h3 h1 h2 hw
    rw [h3]
    have e : (⟨2 * (n + 1) + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = ⟨2 * n + 3, by omega⟩ := Fin.ext (by show 2 * (n + 1) + 1 = 2 * n + 3; omega)
    rw [e]
    rw [Int.toNat_of_nonneg hw] at h1
    linarith

theorem pf_rho_le [NeZero r] (h : IsChain (kLetters A Ai Ci) mu) (i : Fin s) :
    pairRho mu i.val ≤ mu ⟨2 * i.val + 1, by omega⟩ (0 : Fin r).succ + pairW mu i.val := by
  obtain ⟨hW, -, hw, -, -, -, -, -⟩ := pair_top h i
  have h1 := strip_first hW
  rw [Int.toNat_of_nonneg hw] at h1
  unfold pairRho
  rw [finPos_eq (2 * s + 1) (2 * i.val + 2) (by omega)]
  exact h1

theorem pf_u_ge [NeZero r] (h : IsChain (kLetters A Ai Ci) mu) (i : Fin s) :
    pairSg mu Ai i - mu ⟨2 * i.val + 1, by omega⟩ (0 : Fin r).succ ≤ pairO mu Ai i - pairRho mu i.val := by
  have h1 := pf_rho_le h i
  have hs : pairSg mu Ai i = pairO mu Ai i - pairW mu i.val := rfl
  linarith

theorem pf_rho_le_c [NeZero r] (h : IsChain (kLetters A Ai Ci) mu) (i : Fin s) :
    pairRho mu i.val ≤ pairC mu i.val ∧ pairRho mu i.val ≤ pairC mu (i.val + 1) := by
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := pair_top h i
  unfold pairRho
  rw [finPos_eq (2 * s + 1) (2 * i.val + 2) (by omega)]
  exact ⟨h1 0 (by simp), h2 0 (by simp)⟩

theorem pf_d_le (h : IsPair A Ai Ci mu lam) (hr : s + 1 ≤ r) :
    pairD mu lam ≤ pairC mu s + ∑ i, (Ci i : ℤ) - ∑ i : Fin s, pairN (s := s) lam i := by
  obtain ⟨hch, hint⟩ := h
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 + s := ⟨r - 1 - s, by omega⟩
  set ka : Fin (q + 1 + s) → ℤ := fun t => mu (Fin.last _) t.succ with hka
  let L : ℕ → ℤ := fun t => if h : t < q + 1 + s then lam ⟨t, h⟩ else 0
  let K : ℕ → ℤ := fun t => if h : t < q + 1 + s then ka ⟨t, h⟩ else 0
  have hlast : (Fin.last (2 * s + 1) : Fin (2 * s + 1 + 1)) = ⟨2 * s + 1, by omega⟩ := rfl
  have hD : pairD mu lam = ∑ t ∈ range (q + 1 + s), (L t - K t) := by
    unfold pairD pairTail
    rw [finPos_eq (2 * s + 1) (2 * s + 1) (by omega), ← Finset.sum_sub_distrib]
    rw [← Fin.sum_univ_eq_sum_range (fun t => L t - K t)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [L, K, dif_pos t.2, hka, hlast]
  have hmass := pf_mass hch s le_rfl
  have hmass' : pfMass ka ≤ ∑ i, (Ci i : ℤ) := by
    have e : ∀ x : Fin s, (if x.val < s then (Ci x : ℤ) else 0) = Ci x := fun x => if_pos x.2
    rw [Finset.sum_congr rfl fun x _ => e x] at hmass
    exact hmass
  rw [hD, Finset.sum_range_add]

  have hup : ∑ t ∈ range (q + 1), (L t - K t) ≤ L 0 - K q := pf_tele L K q fun t ht => by
    simp only [L, K, dif_pos (show t + 1 < q + 1 + s by omega), dif_pos (show t < q + 1 + s by omega), hka]
    have := (hint ⟨t + 1, by omega⟩).2
    have e : (⟨t + 1, by omega⟩ : Fin (q + 1 + s)).castSucc = (⟨t, by omega⟩ : Fin (q + 1 + s)).succ := Fin.ext rfl
    rw [e] at this
    exact this
  have hL0 : L 0 ≤ pairC mu s := by
    simp only [L, dif_pos (show 0 < q + 1 + s by omega)]
    have := (hint ⟨0, by omega⟩).2
    unfold pairC
    rw [finPos_eq (2 * s + 1) (2 * s + 1) (by omega)]
    exact this
  have hKq : 0 ≤ K q := by
    simp only [K, dif_pos (show q < q + 1 + s by omega), hka]
    have hM : ∀ i, Ai i ≤ ∑ i, Ai i + ∑ i, Ci i := fun i =>
      le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_right _ _)
    have hM' : ∀ i, Ci i ≤ ∑ i, Ai i + ∑ i, Ci i := fun i =>
      le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_left _ _)
    have := (pc_shape hM hM' hch (Fin.last _) (⟨q, by omega⟩ : Fin (q + 1 + s)).succ).2.1
    apply this
    simp only [Fin.val_succ, Fin.val_last, pcL]
    omega

  have hlowL : ∑ x ∈ range s, L (q + 1 + x) = -∑ i : Fin s, pairN (s := s) lam i := by
    rw [← Fin.sum_univ_eq_sum_range (fun x => L (q + 1 + x)), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold pairN
    have e : q + 1 + s - s + i.val = q + 1 + i.val := by omega
    simp only [L, e, neg_neg]
  have hlowK : -∑ x ∈ range s, K (q + 1 + x) ≤ pfMass ka := by
    have h1 : -∑ x ∈ range s, K (q + 1 + x) ≤ ∑ x ∈ range s, max 0 (-(K (q + 1 + x))) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun x _ => le_max_right _ _
    have h2 : ∑ t ∈ range (q + 1 + s), max 0 (-(K t)) = pfMass ka := by
      unfold pfMass
      rw [← Fin.sum_univ_eq_sum_range (fun t => max 0 (-(K t)))]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [K, dif_pos t.2]
    have h3 : ∑ x ∈ range s, max 0 (-(K (q + 1 + x))) ≤ ∑ t ∈ range (q + 1 + s), max 0 (-(K t)) := by
      rw [Finset.sum_range_add]
      have : 0 ≤ ∑ t ∈ range (q + 1), max 0 (-(K t)) := Finset.sum_nonneg fun _ _ => le_max_left _ _
      linarith
    linarith
  have hsplit : ∑ x ∈ range s, (L (q + 1 + x) - K (q + 1 + x)) =
      ∑ x ∈ range s, L (q + 1 + x) - ∑ x ∈ range s, K (q + 1 + x) := Finset.sum_sub_distrib _ _
  rw [hsplit, hlowL]
  linarith

theorem pf_X (h : IsPair A Ai Ci mu lam) (hr : s + 1 ≤ r) (La : ℝ)
    (hK : ∀ i : Fin s, (Ci i : ℝ) * (1 - La / ((r : ℝ) + 1)) ≤ ((pairN (s := s) lam i : ℤ) : ℝ)) :
    ((pairD mu lam : ℤ) : ℝ) ≤ ((pairC mu s : ℤ) : ℝ) + La / ((r : ℝ) + 1) * ∑ i, (Ci i : ℝ) := by
  have h1 := pf_d_le h hr
  have h2 : ((pairD mu lam : ℤ) : ℝ) ≤ ((pairC mu s : ℤ) : ℝ) + ∑ i, (Ci i : ℝ) - ∑ i : Fin s, ((pairN (s := s) lam i : ℤ) : ℝ) := by
    have := (Int.cast_le (R := ℝ)).2 h1
    push_cast at this
    exact this
  have h3 : ∑ i : Fin s, (Ci i : ℝ) * (1 - La / ((r : ℝ) + 1)) ≤ ∑ i : Fin s, ((pairN (s := s) lam i : ℤ) : ℝ) :=
    Finset.sum_le_sum fun i _ => hK i
  have h4 : ∑ i : Fin s, (Ci i : ℝ) * (1 - La / ((r : ℝ) + 1)) =
      ∑ i, (Ci i : ℝ) - La / ((r : ℝ) + 1) * ∑ i, (Ci i : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.WittPNe
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.Pf14

theorem wittVector_prime_ne_zero (p n' : ℕ) [Fact p.Prime] : ((p : ℕ) : WF p n') ≠ 0 := by
  intro h
  have h1 := WittVector.coeff_p_one (p := p) (R := GaloisField p n')
  rw [h] at h1
  simp at h1

theorem planeAt : PlaneAt := by
  intro p n' _ W Qq _ _ _ _ _ m φ h g g' e e' hfr hg hg' he he' hpl
  have hp0 : (p : W) ≠ 0 := by
    intro h0
    apply wittVector_prime_ne_zero p n'
    apply φ.injective
    rw [map_natCast, h0, map_zero]
  have hpQ : (p : Qq) ≠ 0 := by
    rw [← map_natCast (algebraMap W Qq)]
    exact fun h1 => hp0 ((IsFractionRing.injective W Qq) (by rw [h1, map_zero]))
  obtain ⟨-, hs, ht⟩ := he
  obtain ⟨-, hs', ht'⟩ := he'
  rw [src_eq φ g hg h] at hs
  rw [src_eq φ g' hg' h] at hs'
  rw [matQ_inv φ g hg] at ht
  rw [matQ_inv φ g' hg'] at ht'
  change e.tgt = colSpan W (h * (Ng φ g).map (algebraMap W Qq) * dD Qq p 1 (m + 1)) at ht
  change e'.tgt = colSpan W (h * (Ng φ g').map (algebraMap W Qq) * dD Qq p 1 (m + 1)) at ht'
  obtain ⟨s, t⟩ := e
  obtain ⟨s', t'⟩ := e'
  simp only at hs hs' ht ht'
  rw [Edge.mk.injEq]
  refine ⟨by rw [hs, hs'], ?_⟩
  rw [ht, ht']
  apply le_antisymm
  · exact tgt_le_of_plane φ 1 hpQ g' g hg' hg h hpl.le
  · exact tgt_le_of_plane φ 1 hpQ g g' hg hg' h hpl.ge

end Formalism.MainNotions.ColumnSystems.Pf
end
end

