module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RealBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupBoundsLeGeneratorConstantMulSize
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem gc_arith (f r L A n s lam lp a b M : ℝ) (hf : 2 ≤ f) (hr : 6 ≤ r) (hL : 2 ≤ L) (hA : 0 ≤ A)
    (hn : 1 ≤ n) (hs : A + f * r * n + 1 ≤ s) (hlam : 0 ≤ lam) (hlp : 0 ≤ lp) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hM : a + b ≤ M) :
    (140 * r * L * A + 10 * L * A + 200 * f * r * n * L ≤ 400 * (f * r * L) * s) ∧
    (2 * (lam + 2 * lp) * s + 400 * (f * r * L) * s + lam * s ≤
      (1009 * (f * r * L) + (3 * L + 2 * M) + 2 * f * r * (lam + 2 * lp) + 31 * (f * r * L)) * s) ∧
    ((lam + 2 * lp) * s + (400 * (f * r * L) * s + 3 * f * r * n * L + 5 * a + b + 2) ≤
      (1009 * (f * r * L) + (3 * L + 2 * M) + 2 * f * r * (lam + 2 * lp) + 31 * (f * r * L)) * s) := by
  have hfr : 12 ≤ f * r := by nlinarith
  have hrf : r ≤ f * r := by nlinarith
  obtain ⟨F, hF⟩ : ∃ F, F = f * r := ⟨_, rfl⟩
  rw [← hF] at hfr hrf hs
  have hFn : F ≤ F * n := by nlinarith
  have hnF : n ≤ F * n := by nlinarith
  have hs3 : 13 ≤ s := by linarith
  have hAs : A ≤ s := by linarith
  have hns : n ≤ s := by linarith
  have hFns : F * n ≤ s := by linarith
  have hZ : 24 ≤ F * L := by nlinarith
  have hLZ : L ≤ F * L := by nlinarith
  have hrL : r * L ≤ F * L := by nlinarith
  have hZs : 24 ≤ F * L * s := by nlinarith
  have h1 : r * L * A ≤ F * L * s := mul_le_mul hrL hAs hA (by linarith)
  have h2 : L * A ≤ F * L * s := mul_le_mul hLZ hAs hA (by linarith)
  have h3 : F * L * n ≤ F * L * s := mul_le_mul_of_nonneg_left hns (by linarith)
  have hLs : 0 ≤ L * s := by positivity
  have hM0 : 0 ≤ M := by linarith
  have hMs : M * 13 ≤ M * s := mul_le_mul_of_nonneg_left hs3 hM0
  have hlams : 0 ≤ lam * s := by positivity
  have hlps : 0 ≤ lp * s := by positivity
  have h4 : 12 * (lam * s) ≤ F * (lam * s) := mul_le_mul_of_nonneg_right hfr hlams
  have h5 : 12 * (lp * s) ≤ F * (lp * s) := mul_le_mul_of_nonneg_right hfr hlps
  have e : (1009 * (f * r * L) + (3 * L + 2 * M) + 2 * f * r * (lam + 2 * lp) + 31 * (f * r * L)) * s =
      1040 * (F * L * s) + 3 * (L * s) + 2 * (M * s) + 2 * (F * (lam * s)) + 4 * (F * (lp * s)) := by
    rw [hF]; ring
  have e1 : 400 * (f * r * L) * s = 400 * (F * L * s) := by rw [hF]; ring
  have e2 : 200 * f * r * n * L = 200 * (F * L * n) := by rw [hF]; ring
  have e3 : 3 * f * r * n * L = 3 * (F * L * n) := by rw [hF]; ring
  have e4 : 140 * r * L * A = 140 * (r * L * A) := by ring
  have e5 : 10 * L * A = 10 * (L * A) := by ring
  have e6 : 2 * (lam + 2 * lp) * s = 2 * (lam * s) + 4 * (lp * s) := by ring
  have e7 : (lam + 2 * lp) * s = lam * s + 2 * (lp * s) := by ring
  rw [e, e1, e2, e3, e4, e5, e6, e7]
  refine ⟨by linarith, by linarith, by linarith⟩

theorem lamStar_nonneg_nat (D : D7) : 0 ≤ lamStar D := by
  unfold lamStar
  have h1 : 0 ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := by
    have := Real.log_natCast_nonneg (D.host.g 0 * D.host.g 1)
    simpa only [Nat.cast_mul] using this
  have h2 : 0 ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) := by
    have := Real.log_natCast_nonneg (D.R.f ^ 2 * D.host.q * D.host.d)
    have e : 4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d =
        ((D.R.f ^ 2 * D.host.q * D.host.d : ℕ) : ℝ) := by push_cast; ring
    rw [e]; exact this
  linarith

theorem sup_bounds_le_Gc : ∀ (D : D7) (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j) (p : ℕ), 2 ≤ large₂.sc.L → 0 < w.n → (140 * D.R.r * large₂.sc.L * absA w + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L ≤ 400 * Zb D large₂ * w.size) ∧ (2 * (lamStar D + 2 * Real.log p) * w.size + 400 * Zb D large₂ * w.size + lamStar D * w.size ≤ WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) p * w.size) ∧ ((lamStar D + 2 * Real.log p) * w.size + (400 * Zb D large₂ * w.size + 3 * D.R.f * D.R.r * w.n * large₂.sc.L + 5 * Real.log (Module.finrank ℚ B.KO) + Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO + 2) ≤ WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) p * w.size) := by
  intro D B large₂ j w p hL hn
  have hf : (2 : ℝ) ≤ D.R.f := by
    have : 2 ≤ D.R.f := by
      unfold Ranks.f Ranks.n
      have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos
      omega
    exact_mod_cast this
  have hr : (6 : ℝ) ≤ D.R.r := by
    have : 6 ≤ D.R.r := by
      unfold Ranks.r
      have := D.R.two_le_m
      have := D.R.m_add_three_le_k
      omega
    exact_mod_cast this
  have hA : 0 ≤ absA w := by unfold absA; positivity
  have hn' : (1 : ℝ) ≤ w.n := by exact_mod_cast hn
  have hs : absA w + (D.R.f : ℝ) * D.R.r * w.n + 1 ≤ w.size := by
    unfold WeightFamilies.Wt.size absA
    have hm : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    have h0 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * w.n := by positivity
    have : (D.R.f : ℝ) * D.R.r * w.n ≤
        (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hm h0]
    linarith
  have hb : 0 ≤ Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    rw [Real.log_abs]
    exact Real.log_intCast_nonneg _
  unfold WeightAlgebra.Gc Zb
  exact gc_arith _ _ _ _ _ _ _ _ _ _ _ hf hr hL hA hn' hs (lamStar_nonneg_nat D)
    (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg _) hb (le_max_left _ _)

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRunParametersAtTypePrimesProduct
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunParametersAtRecord

theorem lower_real (R P d a r q : ℝ) (hR : 0 ≤ R) (hd : 1 ≤ d) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (h1 : 90 * (a + 1) ≤ P) (h2 : r ≤ P) (hq : R ^ 4 * P ^ 3 * d ^ 2 ≤ q) :
    R ^ 4 * (90 * (a + d)) * d * r ≤ q := by
  have hP : 1 ≤ P := by linarith
  have e1 : 90 * (a + d) ≤ P * d := by nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : 0 ≤ d), mul_le_mul_of_nonneg_left hd ha]
  have e2 : r ≤ P ^ 2 := by nlinarith
  refine le_trans ?_ hq
  have hd0 : 0 ≤ d := by linarith
  have hP0 : 0 ≤ P := by linarith
  calc R ^ 4 * (90 * (a + d)) * d * r ≤ R ^ 4 * (P * d) * d * P ^ 2 := by gcongr
    _ = R ^ 4 * P ^ 3 * d ^ 2 := by ring

theorem run_at_record : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (S : Scal B) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → EtaleWeightGaps.PageSupp D large₂ B C2 A2 nW S wL → RunOK D.host.E D.R.r (WeightAlgebra.DF wL) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL))) D.R.m ∧ 8100 * Real.pi * wL.n * (D.R.m : ℝ) ^ 4 * (I2.dstar (E := D.host.E) D.R.m : ℝ) ^ 4 * I2.RR (E := D.host.E) / (D.host.g 0 * D.host.g 1 : ℕ) ≤ cc D large₂ C2 A2 CR wL ∧ p14 D.host.E D.R.r wL.n D.R.m ≤ (D.R.f * D.R.r * nW * Real.log ((D.host.g 0 : ℝ) * D.host.g 1) + nW * (Real.log 24 + D.R.f * D.R.m * Real.log (4 * D.R.f * D.R.m)) + (D.R.r + 2) * Real.log 2) / 2 ∧ D.R.f * D.R.r * (D.R.r + 1) ≤ 2 * wL.n := by
  intro D B P j X K Ch Ah Cq Aq S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp ht hPg hSu
  obtain ⟨hA, hS, h3, -, -⟩ := hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcol, -, hL, -, -, -, -, -, -, h40, -, -, -, hd⟩ := hS
  obtain ⟨hq1, -, -, -, -, hq6⟩ := h3
  rw [Real.rpow_zero, one_mul] at hq1
  obtain ⟨h13, -, hf2, hr8, hDF⟩ := hSu
  have hn : wL.n = nW := hL.1
  have hC1 : H.C1 = C2 := ht.1
  rw [hC1] at hd
  have hCR : CR = 7 := ht.2.2.2.2.2.1
  have hA2 : 12 ≤ A2 := ht.2.2.2.2.2.2.2.1
  have hf := hostSize_f D
  have hrd := hostSize_rd D
  have h16 := EtaleWeightGaps.sixteen_le_rdE_of_parA hA
  have hm4 := EtaleWeightGaps.lift_index_pow_four_le_degree hPg
  have hf8 := D.eight_le_f
  have hm2 := D.R.two_le_m
  have hRR : WeightFamilies.RRv D CR = I2.RR (E := D.host.E) := by
    rw [hCR]
    unfold WeightFamilies.RRv I2.RR
    rw [hrd]
    exact_mod_cast Real.rpow_natCast D.host.rdE 7
  have hRR0 : 0 ≤ I2.RR (E := D.host.E) := by
    unfold I2.RR
    rw [hrd]
    positivity
  have hZ1 : 1 ≤ zBase large₂ := WeightFamilies.one_le_zBase large₂
  have h12 : WeightAlgebra.sizeConstantAtParamsWeight D nW ≤ WeightFamilies.PPv D large₂ C2 A2 := by
    refine le_trans hd.2.2.2.2.2.2.2.2.1 ?_
    unfold WeightFamilies.PPv
    refine mul_le_mul_of_nonneg_left ?_ (by linarith [hd.1])
    change zBase large₂ ^ 4 ≤ _
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by push_cast; linarith)
  have h90 : 90 * ((D.R.f : ℝ) * D.R.r + 1) ≤ WeightFamilies.PPv D large₂ C2 A2 := le_trans (le_max_left _ _) h12
  have hf8' : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf8
  have hr8' : (8 : ℝ) ≤ D.R.r := by exact_mod_cast hr8
  have hDF' : (3 : ℝ) ≤ (WeightAlgebra.DF wL : ℝ) := by exact_mod_cast hDF
  have hrP : (D.R.r : ℝ) ≤ WeightFamilies.PPv D large₂ C2 A2 := by nlinarith
  have hq2 : (2 : ℝ) ≤ (qq D : ℝ) := by
    have : (0 : ℝ) ≤ ((WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL : ℝ) := by positivity
    linarith
  have hq2' : 2 ≤ qq D := by exact_mod_cast hq2
  have hg0 : 2 ≤ D.host.g 0 := le_trans hq2' (min_le_left _ _)
  have hg1 : 2 ≤ D.host.g 1 := le_trans hq2' (min_le_right _ _)
  have hqg : qq D ≤ D.host.g 0 * D.host.g 1 :=
    le_trans (min_le_left _ _) (Nat.le_mul_of_pos_right _ (by omega))
  have hqg' : (qq D : ℝ) ≤ ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by exact_mod_cast hqg
  have hds : (I2.dstar (E := D.host.E) D.R.m : ℝ) = 2 * (D.R.f : ℝ) * (D.R.m : ℝ) := by
    unfold I2.dstar
    rw [hf]
    push_cast
    ring
  refine ⟨?_, ?_, ?_, by omega⟩
  · have key := GlobalTheory.RunParametersOfLower.runOK_of_le D.host.E D.R.r (WeightAlgebra.DF wL) (D.host.g 0 * D.host.g 1) D.R.m (by omega)
      (by rw [hf]; nlinarith) (by omega) (by rw [hf]; exact_mod_cast hm4) (by rw [hf, hrd]; exact hf2)
      (by rw [hrd]; exact h16)
      (by
        rw [hf]
        rw [hRR] at hq1
        exact lower_real _ _ _ _ _ _ hRR0 (by linarith) (by positivity) (by positivity) h90 hrP (hq1.trans hqg'))
    rw [hf] at key
    exact key
  · unfold cc
    rw [hRR, hds, hn]
    have a1 : 16200 * Real.pi * (nW : ℝ) * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 ≤
        WeightFamilies.PPv D large₂ C2 A2 := le_trans (le_max_left _ _) h13
    have a0 : 0 ≤ 8100 * Real.pi * (nW : ℝ) * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 := by positivity
    have a2 : 8100 * Real.pi * (nW : ℝ) * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 ≤
        WeightFamilies.PPv D large₂ C2 A2 := by linarith
    have hP0 : 0 ≤ WeightFamilies.PPv D large₂ C2 A2 := le_trans a0 a2
    have a3 : WeightFamilies.PPv D large₂ C2 A2 ≤ WeightFamilies.PPv D large₂ C2 A2 * (WeightAlgebra.DF wL : ℝ) ^ 2 :=
      le_mul_of_one_le_right hP0 (one_le_pow₀ (by linarith))
    refine div_le_div₀ (by positivity) ?_ (by linarith) hqg'
    rw [mul_comm _ (I2.RR (E := D.host.E)), mul_assoc (I2.RR (E := D.host.E))]
    exact mul_le_mul_of_nonneg_left (a2.trans a3) hRR0
  · unfold p14
    rw [hds, hn]
    have g0' : (2 : ℝ) ≤ D.host.g 0 := by exact_mod_cast hg0
    have g1' : (2 : ℝ) ≤ D.host.g 1 := by exact_mod_cast hg1
    have g4 : (4 : ℝ) ≤ (D.host.g 0 : ℝ) * D.host.g 1 := by nlinarith
    have b1 : Real.log Real.pi ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) :=
      Real.log_le_log Real.pi_pos (by linarith [Real.pi_le_four])
    have b0 : 0 ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := Real.log_nonneg (by linarith)
    have hW : (1 : ℝ) ≤ nW := by exact_mod_cast (by omega : 1 ≤ nW)
    have b2 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * nW :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) hW
    have b3 := le_mul_of_one_le_left b0 b2
    have e1 : 2 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) = 4 * D.R.f * D.R.m := by ring
    have e2 : 2 * (D.R.f : ℝ) * (D.R.m : ℝ) / 2 = D.R.f * D.R.m := by ring
    rw [e1, e2]
    linarith

end GlobalTheory.RunParametersAtRecord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunWeights

theorem size_le_mul {D : D7} {j : ℕ} (x z : WeightFamilies.Wt D j) (c : ℕ) (hc : 1 ≤ c)
    (h1 : ∀ τ i, x.aP τ i ≤ c * z.aP τ i) (h2 : ∀ τ i, x.aM τ i ≤ c * z.aM τ i) (h3 : x.n ≤ c * z.n) :
    x.size ≤ (c : ℝ) * z.size := by
  have hK : (0 : ℝ) ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) := by positivity
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hS : (∑ τ, ((∑ i, (x.aP τ i : ℝ)) + ∑ i, (x.aM τ i : ℝ))) ≤
      (c : ℝ) * ∑ τ, ((∑ i, (z.aP τ i : ℝ)) + ∑ i, (z.aM τ i : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => ?_
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    refine add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun i _ => ?_)
    · exact_mod_cast h1 τ i
    · exact_mod_cast h2 τ i
  have hn : (x.n : ℝ) ≤ (c : ℝ) * z.n := by exact_mod_cast h3
  have hKn := mul_le_mul_of_nonneg_left hn hK
  unfold WeightFamilies.Wt.size
  nlinarith

theorem DF_le {D : D7} {j : ℕ} (x z : WeightFamilies.Wt D j)
    (h1 : ∀ τ i, x.aP τ i ≤ z.aP τ i) (h2 : ∀ τ i, x.aM τ i ≤ z.aM τ i) : WeightAlgebra.DF x ≤ WeightAlgebra.DF z := by
  unfold WeightAlgebra.DF WeightAlgebra.degP
  exact Finset.sum_le_sum fun τ _ =>
    add_le_add (Finset.sum_le_sum fun i _ => h1 τ i) (Finset.sum_le_sum fun i _ => h2 τ i)

theorem weights_below : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), 1 ≤ j → FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → (∀ w ∈ ({wL, wF, X.wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)), WeightAlgebra.DF w ≤ WeightAlgebra.DF ka ∧ w.n ≤ ka.n ∧ D.R.r ≤ w.n ∧ w.LastPos) ∧ (∀ w ∈ ({wF, X.wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)), 8 * D.R.f * D.R.r + 4 ≤ w.n) ∧ (∀ w2, IsG2 wL wF w2 → WeightAlgebra.DF w2 ≤ WeightAlgebra.DF ka ∧ w2.n ≤ ka.n ∧ w2.size ≤ ((WeightFamilies.dimY D j : ℝ) + 4) * wL.size) ∧ (∀ w1, IsDoubledWeightWithShift wL w1 nW → WeightAlgebra.DF w1 ≤ WeightAlgebra.DF ka ∧ w1.n ≤ ka.n ∧ w1.size ≤ 2 * wL.size) := by
  intro D B P j X large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hj hH
  unfold FamilyHypotheses.HypPage at hH
  obtain ⟨_, hSet, _, _, _⟩ := hH
  unfold SetC at hSet
  obtain ⟨hkan, _, _, hh0, _, hlastP, _, _, _, hnP8, hnPW, _, _, hnV, hL, hF, _, hT0, hDT, h40, hDnW,
    h40n, _, _, _, hDom⟩ := hSet
  obtain ⟨hLn, hLP, _⟩ := hL
  obtain ⟨hFn, hFP, hFM⟩ := hF

  have kaP : ∀ τ i, ka.aP τ i = Tn * wL.aP τ i + wF.aP τ i := fun τ i => by
    have e := hFP τ i
    have e' : ((ka.aP τ i : ℕ) : ℤ) = ((Tn * wL.aP τ i + wF.aP τ i : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast e'
  have kaM : ∀ τ i, ka.aM τ i = Tn * wL.aM τ i + wF.aM τ i := fun τ i => by
    have e := hFM τ i
    have e' : ((ka.aM τ i : ℕ) : ℤ) = ((Tn * wL.aM τ i + wF.aM τ i : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast e'
  have kan : ka.n = nP + Tn * nW := by rw [hkan, hnV]
  have f0P : ∀ τ i, (X.wF0 wL wF).aP τ i = wF.aP τ i + WeightFamilies.dimY D j * wL.aP τ i := fun _ _ => rfl
  have f0M : ∀ τ i, (X.wF0 wL wF).aM τ i = wF.aM τ i + WeightFamilies.dimY D j * wL.aM τ i := fun _ _ => rfl
  have f0n : (X.wF0 wL wF).n = wF.n + WeightFamilies.dimY D j * wL.n := rfl
  have hT1 : 1 ≤ Tn := hT0
  have hT2 : 2 ≤ Tn := by omega
  have hD4 : WeightFamilies.dimY D j + 4 ≤ Tn := by omega

  have hf : 0 < D.R.f := by
    obtain ⟨hC, hCZ, _⟩ := hDom
    have hZ : (0 : ℝ) < Zb D large₂ := lt_of_lt_of_le (by positivity) hCZ
    unfold Zb at hZ
    rcases Nat.eq_zero_or_pos D.R.f with h | h
    · simp [h] at hZ
    · exact h
  have hrP : D.R.r ≤ nP := by
    have e : 8 * D.R.f * D.R.r = 8 * (D.R.f * D.R.r) := by ring
    have := Nat.mul_le_mul hf (le_refl D.R.r)
    omega

  have leKa : ∀ w : WeightFamilies.Wt D j, (∀ τ i, w.aP τ i ≤ ka.aP τ i) → (∀ τ i, w.aM τ i ≤ ka.aM τ i) →
      WeightAlgebra.DF w ≤ WeightAlgebra.DF ka := fun w a b => DF_le w ka a b

  have kaLast : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 → 2 * Tn * Tn ≤ ka.aP τ i := by
    intro τ i hi
    have e := hlastP τ i hi
    have e' : (2 * (Tn : ℝ) * Tn) ≤ ka.aP τ i := by nlinarith
    exact_mod_cast e'

  have wLLast : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 →
      1 ≤ wL.aP τ i ∧ ((Tn + WeightFamilies.dimY D j + 2 : ℕ) : ℤ) * wL.aP τ i ≤
        (ka.aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * nW - 2 * D.R.r := by
    intro τ i hi
    have e := hLP τ i
    unfold gapZ at e
    rw [dite_eq_right (by omega), if_neg (by omega)] at e
    unfold Tp at e
    have hb : (0 : ℤ) < ((Tn + WeightFamilies.dimY D j + 2 : ℕ) : ℤ) := by positivity
    rw [Int.fdiv_eq_ediv, if_pos (Or.inl hb.le), sub_zero] at e
    have hk := kaLast τ i hi
    have hTT := Nat.mul_le_mul hT2 (le_refl Tn)
    constructor
    · have : (1 : ℤ) ≤ (wL.aP τ i : ℤ) := by
        rw [e, Int.le_ediv_iff_mul_le hb]
        have hk' : ((2 * Tn * Tn : ℕ) : ℤ) ≤ (ka.aP τ i : ℤ) := by exact_mod_cast hk
        have hTT' : ((2 * Tn : ℕ) : ℤ) ≤ ((Tn * Tn : ℕ) : ℤ) := by exact_mod_cast hTT
        have hDnW' : (((WeightFamilies.dimY D j + 2) * nW + 2 * D.R.r : ℕ) : ℤ) ≤ (Tn : ℤ) := by exact_mod_cast hDnW
        have hDT' : ((WeightFamilies.dimY D j : ℕ) : ℤ) ≤ (Tn : ℤ) := by exact_mod_cast hDT
        push_cast at hk' hTT' hDnW' hDT' ⊢
        nlinarith
      exact_mod_cast this
    · rw [e]
      exact Int.mul_ediv_self_le hb.ne'
  have wFLast : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 → 1 ≤ wF.aP τ i := by
    intro τ i hi
    obtain ⟨_, h2⟩ := wLLast τ i hi
    have e := hFP τ i
    have h0' : (0 : ℤ) ≤ (WeightFamilies.dimY D j : ℤ) * wL.aP τ i := by positivity
    have h1' : (0 : ℤ) ≤ (WeightFamilies.dimY D j : ℤ) * nW := by positivity
    have h40' : (40 : ℤ) ≤ nW := by exact_mod_cast h40n
    have : (1 : ℤ) ≤ (wF.aP τ i : ℤ) := by
      push_cast at h2
      nlinarith
    exact_mod_cast this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · refine ⟨leKa _ (fun τ i => ?_) (fun τ i => ?_), ?_, ?_, ?_⟩
      · have := Nat.mul_le_mul hT1 (le_refl (w.aP τ i)); rw [kaP]; omega
      · have := Nat.mul_le_mul hT1 (le_refl (w.aM τ i)); rw [kaM]; omega
      · have := Nat.mul_le_mul hT1 (le_refl nW); rw [kan, hLn]; omega
      · rw [hLn]; omega
      · intro τ i hi; exact (wLLast τ i hi).1
    · refine ⟨leKa _ (fun τ i => ?_) (fun τ i => ?_), ?_, ?_, ?_⟩
      · rw [kaP]; omega
      · rw [kaM]; omega
      · rw [kan, hFn]; omega
      · rw [hFn]; omega
      · intro τ i hi; exact wFLast τ i hi
    · refine ⟨leKa _ (fun τ i => ?_) (fun τ i => ?_), ?_, ?_, ?_⟩
      · have := Nat.mul_le_mul hDT (le_refl (wL.aP τ i)); rw [kaP, f0P]; omega
      · have := Nat.mul_le_mul hDT (le_refl (wL.aM τ i)); rw [kaM, f0M]; omega
      · have := Nat.mul_le_mul hDT (le_refl nW); rw [kan, f0n, hFn, hLn]; omega
      · rw [f0n, hFn]; omega
      · intro τ i hi
        have := wFLast τ i hi
        rw [f0P]; omega
    · refine ⟨le_refl _, le_refl _, ?_, ?_⟩
      · rw [kan]; omega
      · intro τ i hi
        have := kaLast τ i hi
        have hTT := Nat.mul_le_mul hT2 hT1
        have e : 2 * Tn * Tn = 2 * (Tn * Tn) := by ring
        omega
  · intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · rw [hFn]; omega
    · rw [f0n, hFn]; omega
    · rw [kan]; omega
  · intro w2 hw2
    obtain ⟨h2n, h2P, h2M⟩ := hw2
    have bP : ∀ τ i, w2.aP τ i ≤ (WeightFamilies.dimY D j + 4) * wL.aP τ i := fun τ i => by
      have := h2P τ i; omega
    have bM : ∀ τ i, w2.aM τ i ≤ (WeightFamilies.dimY D j + 4) * wL.aM τ i := fun τ i => by
      have := h2M τ i; omega
    have bn : w2.n ≤ (WeightFamilies.dimY D j + 4) * wL.n := by omega
    refine ⟨leKa _ (fun τ i => ?_) (fun τ i => ?_), ?_, ?_⟩
    · have := Nat.mul_le_mul hD4 (le_refl (wL.aP τ i)); have := bP τ i; rw [kaP]; omega
    · have := Nat.mul_le_mul hD4 (le_refl (wL.aM τ i)); have := bM τ i; rw [kaM]; omega
    · have := Nat.mul_le_mul hD4 (le_refl nW); rw [kan]; rw [hLn] at bn; omega
    · have := size_le_mul w2 wL (WeightFamilies.dimY D j + 4) (by omega) bP bM bn
      push_cast at this
      exact this
  · intro w1 hw1
    obtain ⟨h1n, h1P, h1M⟩ := hw1
    have bn : w1.n ≤ 2 * wL.n := by omega
    refine ⟨leKa _ (fun τ i => ?_) (fun τ i => ?_), ?_, ?_⟩
    · have := Nat.mul_le_mul hT2 (le_refl (wL.aP τ i)); have := h1P τ i; rw [kaP]; omega
    · have := Nat.mul_le_mul hT2 (le_refl (wL.aM τ i)); have := h1M τ i; rw [kaM]; omega
    · have := Nat.mul_le_mul hT2 (le_refl nW); rw [kan]; rw [hLn] at bn; omega
    · have := size_le_mul w1 wL 2 (by norm_num) (fun τ i => (h1P τ i).le) (fun τ i => (h1M τ i).le) bn
      push_cast at this
      exact this

end GlobalTheory.RunWeights
end
end

