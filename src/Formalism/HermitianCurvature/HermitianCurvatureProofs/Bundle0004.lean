module

public import Formalism.HermitianCurvature.StatementSz
public import Formalism.HermitianCurvature.Bundle0001
public import Formalism.HermitianCurvature.StatementG

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MassRatioFormula
section
namespace Formalism.FourierDecayAlt.P.Sz1

open Finset Formalism.FourierDecayAlt.Sz

lemma half_eq (r : ℕ) : (2 * r + 2) * (2 * r + 2 - 1) / 2 = (r + 1) * (2 * r + 1) := by
  have h : (2 * r + 2) * (2 * r + 2 - 1) = 2 * ((r + 1) * (2 * r + 1)) := by
    have h1 : 2 * r + 2 - 1 = 2 * r + 1 := by omega
    rw [h1]; ring
  rw [h]; simp

lemma two_sum_Ioc (k p : ℕ) : 2 * ∑ M ∈ Ioc k (k + p), M = 2 * (p * k) + p * (p + 1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [← Nat.add_assoc, Finset.sum_Ioc_succ_top (by omega), mul_add, ih]; ring

lemma sum_Ioc_odd (k r : ℕ) :
    ∑ M ∈ Ioc k (k + (2 * r + 1)), M = (2 * r + 1) * k + (r + 1) * (2 * r + 1) := by
  have h := two_sum_Ioc k (2 * r + 1)
  have h2 : 2 * ((2 * r + 1) * k) + (2 * r + 1) * (2 * r + 1 + 1) =
      2 * ((2 * r + 1) * k + (r + 1) * (2 * r + 1)) := by ring
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

lemma glCard_eq (p : ℕ) (q : ℝ) (hq : q ≠ 0) :
    glCard p q = q ^ (p * p) * ∏ i ∈ range p, (1 - (q ^ (i + 1))⁻¹) := by
  unfold glCard
  rw [← Finset.prod_range_reflect (fun i => (1 - (q ^ (i + 1))⁻¹)) p]
  have h : ∀ j ∈ range p, q ^ p - q ^ j = q ^ p * (1 - (q ^ (p - 1 - j + 1))⁻¹) := by
    intro j hj
    have hj' : j < p := Finset.mem_range.mp hj
    have e1 : p - 1 - j + 1 = p - j := by omega
    have e2 : q ^ p = q ^ j * q ^ (p - j) := by rw [← pow_add]; congr 1; omega
    have hne : q ^ (p - j) ≠ 0 := pow_ne_zero _ hq
    rw [e1, e2]; field_simp
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← pow_mul]

lemma prod_split (k d : ℕ) (q : ℝ) :
    ∏ i ∈ range (k + d), (1 - (q ^ (i + 1))⁻¹) =
      (∏ i ∈ range k, (1 - (q ^ (i + 1))⁻¹)) * ∏ j ∈ Ioc k (k + d), (1 - (q ^ j)⁻¹) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, Finset.prod_range_succ, Finset.prod_Ioc_succ_top (by omega), ih, mul_assoc]

lemma prod_ne_zero (k : ℕ) (q : ℝ) (hq : 1 < q) :
    ∏ i ∈ range k, (1 - (q ^ (i + 1))⁻¹) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  have h1 : 1 < q ^ (i + 1) := one_lt_pow₀ hq (by omega)
  have h2 : (q ^ (i + 1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  linarith

lemma glCard_ne_zero (k : ℕ) (q : ℝ) (hq : 1 < q) : glCard k q ≠ 0 := by
  have hq0 : q ≠ 0 := by linarith
  rw [glCard_eq k q hq0]
  exact mul_ne_zero (pow_ne_zero _ hq0) (prod_ne_zero k q hq)

lemma colIdx_ne_zero (k : ℕ) (q : ℝ) (hq : 1 < q) : colIdx k q ≠ 0 := by
  have hq0 : q ≠ 0 := by linarith
  unfold colIdx
  exact div_ne_zero (glCard_ne_zero k q hq) (pow_ne_zero _ hq0)

lemma vol_chain {ι : Type} [Fintype ι] (S : SizeData ι) (hM : S.MassRatios) (d : ℕ)
    (hd : S.k + d ≤ S.n) :
    S.vol (S.k + d) =
      ((S.v / Real.pi) ^ (∑ M ∈ Ioc S.k (S.k + d), M) *
          ((∏ i ∈ Ico S.k (S.k + d), i.factorial : ℕ) : ℝ)) ^ S.f *
        (S.dF ^ (-(1 / 2 : ℝ))) ^ d * (∏ M ∈ Ioc S.k (S.k + d), S.Lv M) * S.vol S.k := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h := hM (S.k + d + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel, ih (by omega)] at h
    rw [← Nat.add_assoc, h, Finset.sum_Ioc_succ_top (by omega), Finset.prod_Ioc_succ_top (by omega),
      Finset.prod_Ico_succ_top (by omega), pow_add, pow_succ]
    push_cast
    simp only [mul_pow]
    ring

lemma disc_pow (rd : ℝ) (hrd : 0 < rd) (f p : ℕ) :
    ((rd ^ f) ^ (-(1 / 2 : ℝ))) ^ p = (rd ^ (-((p : ℝ) / 2))) ^ f := by
  rw [← Real.rpow_natCast rd f, ← Real.rpow_mul hrd.le, ← Real.rpow_natCast _ p,
    ← Real.rpow_mul hrd.le, ← Real.rpow_natCast _ f, ← Real.rpow_mul hrd.le]
  congr 1; ring

end Formalism.FourierDecayAlt.P.Sz1

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz1

theorem sumRanks : Formalism.FourierDecayAlt.Sz.SumRanks := by
  intro k r m n hm hn
  subst hm
  have hn' : n = k + (2 * r + 1) := by omega
  subst hn'
  have h1 : 2 * r + 2 - 1 = 2 * r + 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [half_eq, sum_Ioc_odd, h1]
  · rw [Nat.card_Ioc]; omega
  · rw [half_eq, h1]; ring

theorem levelExponent : Formalism.FourierDecayAlt.Sz.LevelExponent := by
  intro k r m n hm hn
  subst hm
  have hn' : n = k + 2 * r + 1 := by omega
  subst hn'
  rw [half_eq]
  unfold dimN
  constructor <;> ring

theorem indexRatio : Formalism.FourierDecayAlt.Sz.IndexRatio := by
  intro k r m n q hm hn hq
  have hq0 : q ≠ 0 := by linarith
  have hexp := (levelExponent k r m n hm hn).2
  have hn' : n = k + (2 * r + 1) := by omega
  have hn'' : k + 2 * r + 1 = n := by omega
  unfold rowIdx colIdx
  rw [hn'', glCard_eq n q hq0, glCard_eq k q hq0]
  have hsplit : ∏ i ∈ range n, (1 - (q ^ (i + 1))⁻¹) =
      (∏ i ∈ range k, (1 - (q ^ (i + 1))⁻¹)) * ∏ j ∈ Ioc k n, (1 - (q ^ j)⁻¹) := by
    rw [hn']; exact prod_split k (2 * r + 1) q
  have hG := prod_ne_zero k q hq
  have hpow : q ^ (n * n) = q ^ (k * k) * q ^ dimN k r * q ^ (k * m + m * (m - 1) / 2) := by
    rw [← pow_add, ← pow_add]; congr 1; rw [← sq, ← sq, hexp]
  rw [hsplit, hpow]
  have a1 : q ^ (k * k) ≠ 0 := pow_ne_zero _ hq0
  have a2 : q ^ dimN k r ≠ 0 := pow_ne_zero _ hq0
  have a3 : q ^ (k * (k - 1) / 2) ≠ 0 := pow_ne_zero _ hq0
  generalize (∏ i ∈ range k, (1 - (q ^ (i + 1))⁻¹)) = G at hG ⊢
  generalize (∏ j ∈ Ioc k n, (1 - (q ^ j)⁻¹)) = H
  field_simp

theorem factorialCancel : Formalism.FourierDecayAlt.Sz.FactorialCancel := by
  intro k n hkn
  unfold sfac
  rw [mul_comm]
  exact Finset.prod_range_mul_prod_Ico _ hkn

theorem volumeChain : Formalism.FourierDecayAlt.Sz.VolumeChain := by
  intro ι _ S hOk hM
  have hn : S.n = S.k + (2 * S.r + 1) := by unfold SizeData.n SizeData.m; omega
  have hm1 : S.m - 1 = 2 * S.r + 1 := by unfold SizeData.m; omega
  have hmR : (S.m : ℝ) - 1 = ((2 * S.r + 1 : ℕ) : ℝ) := by unfold SizeData.m; push_cast; ring
  have hsum := (sumRanks S.k S.r S.m S.n rfl rfl).1
  have h := vol_chain S hM (2 * S.r + 1) (by omega)
  rw [← hn, hsum] at h
  have hrd : 0 < S.rd := by unfold SizeData.rd; linarith [hOk.hv]
  have hdF : S.dF = S.rd ^ S.f := hOk.hdF
  have hka : S.v / Real.pi = S.ka⁻¹ := by unfold SizeData.ka; rw [inv_div]
  rw [h, hdF, disc_pow S.rd hrd, hka, inv_pow, hmR]
  simp only [mul_pow]
  ring

theorem massRatioFormula : Formalism.FourierDecayAlt.Sz.PropA := by
  intro ι _ S hOk hM hC
  have hvc := volumeChain ι S hOk hM
  have hkn : S.k ≤ S.n := by unfold SizeData.n SizeData.m; omega
  have hfac : ((∏ i ∈ Ico S.k S.n, i.factorial : ℕ) : ℝ) * (sfac S.k : ℝ) = (sfac S.n : ℝ) := by
    exact_mod_cast factorialCancel S.k S.n hkn
  have hg1 : (1 : ℝ) < S.g1 := by exact_mod_cast (lt_of_lt_of_le one_lt_two hOk.hg1)
  have hg2 : (1 : ℝ) < S.g2 := by exact_mod_cast (lt_of_lt_of_le one_lt_two hOk.hg2)
  have hT : (1 : ℝ) < S.T := by exact_mod_cast (lt_of_lt_of_le one_lt_two hOk.hT)
  have hi1 := indexRatio S.k S.r S.m S.n S.g1 rfl rfl hg1
  have hi2 := indexRatio S.k S.r S.m S.n S.g2 rfl rfl hg2
  have hc1 := colIdx_ne_zero S.k S.g1 hg1
  have hc2 := colIdx_ne_zero S.k S.g2 hg2
  rw [div_eq_iff hc1] at hi1
  rw [div_eq_iff hc2] at hi2
  have hsk : (sfac S.k : ℝ) ≠ 0 := by
    unfold sfac
    exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero i)
  have hTk : (1 : ℝ) < (S.T : ℝ) ^ S.k := one_lt_pow₀ hT (by have := hOk.hk; omega)
  have hTk0 : (S.T : ℝ) ^ S.k ≠ 0 := by linarith
  have hTk1 : (S.T : ℝ) ^ S.k - 1 ≠ 0 := by linarith
  have hVu : ∏ w, S.Vu w ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => (hOk.hVu w).ne'
  have hvol : S.vol S.k ≠ 0 := hOk.hvol.ne'
  have hdim : ∏ w, S.dimPi w = (∏ w, S.Vu w) / (sfac S.k : ℝ) ^ S.f := by
    unfold SizeData.dimPi SizeData.f
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  have hprod : ∏ w, (S.TcritPow w / (S.T : ℝ) ^ S.k) =
      ((S.ka ^ ((S.m - 1) * S.k + S.m * (S.m - 1) / 2))⁻¹ * S.rd ^ (-(((S.m : ℝ) - 1) / 2)) *
        S.g ^ (S.k * S.m + S.m * (S.m - 1) / 2) * (sfac S.n : ℝ) / (S.T : ℝ) ^ S.k) ^ S.f *
        (∏ w, S.dsig w) / (∏ w, S.Vu w) := by
    have h : ∀ w ∈ (Finset.univ : Finset ι), S.TcritPow w / (S.T : ℝ) ^ S.k =
        ((S.ka ^ ((S.m - 1) * S.k + S.m * (S.m - 1) / 2))⁻¹ * S.rd ^ (-(((S.m : ℝ) - 1) / 2)) *
        S.g ^ (S.k * S.m + S.m * (S.m - 1) / 2) * (sfac S.n : ℝ) / (S.T : ℝ) ^ S.k) *
        S.dsig w / S.Vu w := by
      intro w _
      unfold SizeData.TcritPow Sz.TcritPow SizeData.VV
      ring
    rw [Finset.prod_congr rfl h, Finset.prod_div_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ]
    rfl
  have hT1 : (1 - ((S.T : ℝ) ^ S.k)⁻¹) = ((S.T : ℝ) ^ S.k - 1) / (S.T : ℝ) ^ S.k := by
    field_simp
  rw [hprod, hC, hdim]
  unfold SizeData.Dstar SizeData.Ea SizeData.idxRow SizeData.idxCol SizeData.g
  rw [hvc, hi1, hi2, hT1, ← hfac]
  generalize (S.ka ^ ((S.m - 1) * S.k + S.m * (S.m - 1) / 2))⁻¹ = A
  generalize S.rd ^ (-(((S.m : ℝ) - 1) / 2)) = B
  generalize ((∏ i ∈ Ico S.k S.n, i.factorial : ℕ) : ℝ) = F
  generalize (∏ M ∈ Ioc S.k S.n, S.Lv M) = L
  generalize (∏ j ∈ Ioc S.k S.n, (1 - (((S.g1 : ℝ)) ^ j)⁻¹)) = P1
  generalize (∏ j ∈ Ioc S.k S.n, (1 - (((S.g2 : ℝ)) ^ j)⁻¹)) = P2
  generalize (∏ w, S.dsig w) = D
  generalize (∏ w, S.Vu w) = V at hVu ⊢
  generalize colIdx S.k (S.g1 : ℝ) = c1 at hc1 ⊢
  generalize colIdx S.k (S.g2 : ℝ) = c2 at hc2 ⊢
  generalize (sfac S.k : ℝ) = s at hsk ⊢
  generalize (S.T : ℝ) ^ S.k = t at hTk0 hTk1 ⊢
  generalize S.vol S.k = v0 at hvol ⊢
  generalize S.k * S.m + S.m * (S.m - 1) / 2 = e
  simp only [mul_pow, div_pow]
  field_simp

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RecText
section
namespace Formalism.FourierDecayAlt.P.RecText

open Finset Real

theorem geo (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1/2) :
    ∀ i, 1 ≤ i → ∑ t ∈ Icc 2 i, a ^ (t - 1) ≤ 2 * a - 2 * a ^ i := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
    have : a ^ (n + 1) = a ^ n * a := pow_succ a n
    have h0 : 0 ≤ a ^ n := pow_nonneg ha0 n
    nlinarith

theorem recT : Formalism.FourierDecayAlt.RecursionText := by
  refine ⟨Real.exp 9, ?_⟩
  intro r a ε e σ ha0 ha1 hε hεa hra he hσ hrec
  set lam := 1 + ε + 2 * a with hlam
  set Q : ℕ → ℝ := fun k => ∏ j ∈ Icc 1 k, √(1 + e j) with hQdef
  have hQsucc : ∀ k, Q (k + 1) = Q k * √(1 + e (k + 1)) := by
    intro k; simp only [hQdef]; rw [Finset.prod_Icc_succ_top (by omega)]
  have hsq1 : ∀ j, 1 ≤ √(1 + e j) := fun j => by
    rw [Real.one_le_sqrt]; linarith [he j]
  have hQ0 : Q 0 = 1 := by simp [hQdef]
  have hQ1 : ∀ k, 1 ≤ Q k := by
    intro k; induction k with
    | zero => rw [hQ0]
    | succ k ih => rw [hQsucc]; nlinarith [hsq1 (k + 1)]
  have hQmono : Monotone Q := by
    apply monotone_nat_of_le_succ; intro k; rw [hQsucc]; nlinarith [hsq1 (k + 1), hQ1 k]
  have hlam1 : 1 ≤ lam := by linarith
  have hs0 := hσ 0
  have main : ∀ i, i ≤ r + 1 → σ i ≤ lam ^ i * Q i * σ 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hir
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0; simp [hQ0]
      · have hrec' := hrec i hpos hir
        obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        have hk : k + 1 - 1 = k := by omega
        rw [hk] at hrec'
        set M := lam ^ k * Q (k + 1) * σ 0 with hM
        have hM0 : 0 ≤ M := by
          have := pow_nonneg (by linarith : (0:ℝ) ≤ lam) k
          have := hQ1 (k + 1)
          positivity
        have hk' := ih k (by omega) (by omega)
        have h1 : (1 + ε) * √(1 + e (k + 1)) * σ k ≤ (1 + ε) * M := by
          rw [hM, hQsucc]
          have : √(1 + e (k + 1)) * σ k ≤ √(1 + e (k + 1)) * (lam ^ k * Q k * σ 0) :=
            mul_le_mul_of_nonneg_left hk' (Real.sqrt_nonneg _)
          nlinarith
        have h2 : ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * σ (k + 1 - t) ≤
            ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * M := by
          apply Finset.sum_le_sum
          intro t ht
          rw [Finset.mem_Icc] at ht
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha0 _)
          have := ih (k + 1 - t) (by omega) (by omega)
          refine this.trans ?_
          rw [hM]
          have e1 : lam ^ (k + 1 - t) ≤ lam ^ k := pow_le_pow_right₀ hlam1 (by omega)
          have e2 : Q (k + 1 - t) ≤ Q (k + 1) := hQmono (by omega)
          have e3 : 0 ≤ lam ^ (k + 1 - t) := pow_nonneg (by linarith) _
          have e4 : 0 ≤ Q (k + 1 - t) := by linarith [hQ1 (k + 1 - t)]
          have e5 : 0 ≤ lam ^ k := pow_nonneg (by linarith) _
          have := mul_le_mul e1 e2 e4 e5
          exact mul_le_mul_of_nonneg_right this hs0
        have h3 : ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * M ≤ 2 * a * M := by
          rw [← Finset.sum_mul]
          have := geo a ha0 ha1 (k + 1) (by omega)
          have : 0 ≤ a ^ (k + 1) := pow_nonneg ha0 _
          apply mul_le_mul_of_nonneg_right _ hM0
          linarith
        have : lam ^ (k + 1) * Q (k + 1) * σ 0 = lam * M := by rw [hM]; ring
        rw [this]
        calc σ (k + 1) ≤ (1 + ε) * M + 2 * a * M := by linarith
          _ = lam * M := by rw [hlam]; ring
  have hfin := main (r + 1) le_rfl
  have hQsq : Q (r + 1) ^ 2 = ∏ i ∈ Icc 1 (r + 1), (1 + e i) := by
    simp only [hQdef]; rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Real.sq_sqrt]; linarith [he j]
  have hP : 0 ≤ ∏ i ∈ Icc 1 (r + 1), (1 + e i) := by rw [← hQsq]; positivity
  have hsr := hσ (r + 1)
  have step1 : σ (r + 1) ^ 2 ≤ (lam ^ (r + 1)) ^ 2 * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2 := by
    rw [← hQsq]
    have := pow_le_pow_left₀ hsr hfin 2
    calc σ (r + 1) ^ 2 ≤ (lam ^ (r + 1) * Q (r + 1) * σ 0) ^ 2 := this
      _ = _ := by ring
  set x := ((r : ℝ) + 1) * a with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx32 : x ≤ 3 / 2 := by rw [hxdef]; nlinarith
  have step2 : (lam ^ (r + 1)) ^ 2 ≤ Real.exp (6 * x) := by
    rw [← pow_mul]
    have h1 : lam ≤ Real.exp (ε + 2 * a) := by
      have := Real.add_one_le_exp (ε + 2 * a); rw [hlam]; linarith
    have h2 := pow_le_pow_left₀ (by linarith) h1 ((r + 1) * 2)
    refine h2.trans ?_
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have step3 : Real.exp (6 * x) ≤ 1 + Real.exp 9 * x := by
    have ht0 : 0 ≤ 2 / 3 * x := by positivity
    have hc := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (9:ℝ))
      (by linarith : (0:ℝ) ≤ 1 - 2 / 3 * x) ht0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
    have : 6 * x = 2 / 3 * x * 9 := by ring
    rw [this]
    have : 0 ≤ Real.exp 9 := (Real.exp_pos 9).le
    nlinarith
  have : (lam ^ (r + 1)) ^ 2 ≤ 1 + Real.exp 9 * ((r : ℝ) + 1) * a := by
    have := step2.trans step3; rw [hxdef] at this; linarith
  refine step1.trans ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_right this hP

end Formalism.FourierDecayAlt.P.RecText

theorem Formalism.FourierDecayAlt.P.coarseBound : Formalism.FourierDecayAlt.RecursionText := Formalism.FourierDecayAlt.P.RecText.recT
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerBlockPoint
section
open Matrix
open Formalism.FourierDecayAlt.G

namespace Formalism.FourierDecayAlt.P.G4

theorem blk_cc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk A b a e i.castSucc j.castSucc = A i j := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  simp [blk, h]

theorem blk_cl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  have h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
  simp [blk, h, h2]

theorem blk_lc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk A b a e (Fin.last n) j.castSucc = a j := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  have h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
  simp [blk, h, h2]

theorem blk_mul {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) (b a b' a' : Fin n → ℂ) (e e' : ℂ) :
    blk A b a e * blk A' b' a' e' =
      blk (A * A' + Matrix.vecMulVec b a') (A *ᵥ b' + e' • b) (a ᵥ* A' + e • a') (a ⬝ᵥ b' + e * e') := by
  unfold blk
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  congr 2
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply, dotProduct]

theorem upperUni_det {d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) : u.det = 1 := by
  have h : u.BlockTriangular id := fun i j hij => hu.2 i j hij
  rw [Matrix.det_of_isUpperTriangular h]
  simp [hu.1]

theorem superSum_blk {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (b a : Fin (m + 1) → ℂ) (e : ℂ) :
    superSum (blk A b a e) = superSum A + b (Fin.last m) := by
  unfold superSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, blk_cc]
  · rw [Fin.succ_last, blk_cl]

theorem subSum_blk {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (b a : Fin (m + 1) → ℂ) (e : ℂ) :
    subSum (blk A b a e) = subSum A + a (Fin.last m) := by
  unfold subSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, blk_cc]
  · rw [Fin.succ_last, blk_lc]

end Formalism.FourierDecayAlt.P.G4

namespace Formalism.FourierDecayAlt.P

open G4

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.UnitaryInvariantGaussian
section
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.G8

theorem psi_add (β x y : ℂ) : psi β (x + y) = psi β x * psi β y := by
  simp only [psi, mul_add, Complex.add_re, Complex.ofReal_add, Complex.exp_add]

end Formalism.FourierDecayAlt.P.G8

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end

