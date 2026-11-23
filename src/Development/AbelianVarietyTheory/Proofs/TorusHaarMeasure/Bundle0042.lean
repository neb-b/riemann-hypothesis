module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0042
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.PhRec
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.TranscendenceDegreeRatiosCuspFormsComponents
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ValAtAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SetConstantsGoodEmbeddingRecursion
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec

noncomputable section

namespace GlobalTheory.BigRec

section Inst

variable {D : D7} {T : Top D}

variable (h : LawsP T) {j : ℕ} (hj : InR D j)

end Inst


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem bigAt_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (c : ℝ) (large₂ : SizeData₂ D) (CK C1 A1 h0 : ℝ) (Tn nP nW : ℕ), SetC large₂ (recPlus h j hj) CK C1 A1 ka wL wF Tn nP nW h0 → NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G.w i).1) → (j < D.R.m → 0 < G.iet ∧ (recPlus h j hj).NonZeroComp _ G.et ∧ ∃ σ, GoodEmb T.Q.c σ ∧ PhRec h j σ G.w G.iet G.et c) → 0 ≤ c → 2 * c * g0 D ≤ 1 → (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW ∧ ∃ th : (recB h.toLawsCore).Cusp j w1, (recPlus h j hj).NonZeroComp w1 th) → BigAt h j hj hG G := by
  intro D T h j hj hG ka wL wF G c large₂ CK C1 A1 h0 Tn nP nW hS hN hE hc hcg _
  exact ⟨hN, _root_.GlobalTheory.BigTrdeg.trdeg_ratios_record D T h j hj hG ka wL wF G c large₂ CK C1 A1 h0 Tn nP nW hS hN hE hc hcg⟩

end GlobalTheory.BigRec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ThetaArchimedeanDataIndefiniteModels
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

theorem thR_pos_of_rank {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (hr : 0 < D.R.r) : 0 < thR w := by
  have hf : 0 < D.R.f := GlobalTheory.ArchInputs.f_pos D
  have hfE : I2.PT.f D.host.E = D.R.f := GlobalTheory.ArchInputs.finrank_host D
  have hrd := GlobalTheory.ArchInputs.one_le_rd (E := D.host.E)
  have h0 := (D.host.g_prime 0).pos
  have h1 := (D.host.g_prime 1).pos
  unfold thR I2.th I2.RR
  rw [hfE]
  positivity

theorem sq_le_of_mul_le_exp {a b i p q : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (h : a * b ≤ Real.exp (-i * (p - q))) :
    b ^ 2 ≤ Real.exp (2 * (i * q)) / a ^ 2 * Real.exp (-(2 * i * p)) := by
  have h2 := pow_le_pow_left₀ (mul_nonneg ha.le hb) h 2
  rw [← Real.exp_nat_mul] at h2
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), ← Real.exp_add, ← mul_pow, mul_comm b]
  refine h2.trans (le_of_eq ?_)
  congr 1
  push_cast
  ring


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem archAt_of_run : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (EX : ErrX D) (p : ℕ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → j < D.R.m → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → EtaOK h j hj large₂ wL G.iet G.et → Nonempty (GlobalTheory.Shares.ArchAt h j G.w wF Tn (WeightFamilies.c1 D 7 Tn (cc D large₂ C2 A2 7 wL) j)) := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p S nus _ hP hC hjm G hGen hEta
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hP.tie
  have ht : TieC ⟨1, 2, 1, 2, 1, 2, 1, 4, 7⟩ H 1 4 0 11 C2 A2 7 :=
    ⟨t1, t2, t3, t4, t5, rfl, rfl, t6, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  obtain ⟨n1, n2, n3, n4, -, n6, -⟩ := GlobalTheory.ExtraWeight.numbers D _ _ j _ _ 1 4 0 11 large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hP.hyp ht hP.page hjm hj.1 (le_trans (by norm_num) hP.df)
  obtain ⟨-, -, -, -, -, -, ⟨-, -, -, -, -, -, PLam, lNc, -, -, hw1, w2, hG2, th2, -, hth2, -⟩, -⟩ := hC
  obtain ⟨w1, hG1, th1, -, hth1, -⟩ := hw1 hjm
  obtain ⟨⟨g0, hg0, -⟩, hnz⟩ := _root_.GlobalTheory.RunJoin.exists_nonZeroComp_and_ne_zero D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0
    (GlobalTheory.Reg.genFrEx_and_genFromTest _ _ _ _ _ _).1 hP
  obtain ⟨-, -, -, hw, hlow⟩ := hGen
  obtain ⟨hi, ⟨-, het⟩, -, -, harch, -⟩ := hEta
  have hth : 0 < thR wL := thR_pos_of_rank wL (lt_of_lt_of_le (by norm_num) hP.r8)
  have hrows := (GlobalTheory.pageRows_of_pageAt D _ _ j _ large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hP.hyp hP.page hP.ck).1
  have hL : 2 ≤ large₂.sc.L := by
    obtain ⟨_, _, hsz, -⟩ := hP.page
    exact (GlobalTheory.EtaAn.page_rows D large₂ _ hP.hyp.1 hsz).1
  have hrn : D.R.r ≤ ka.n := ((GlobalTheory.RunWeights.weights_below D _ _ j _ large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hj.1
    hP.hyp).1 ka (by simp)).2.2.1
  refine GlobalTheory.ArchInputs.archAt_nonempty D T h j hj large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 7 _ G.N G.w G.iet G.et w1 w2
    th1 th2 hP.hyp hjm hP.r8 n1 n2 n3 n4 n6 hi hG1 hG2
    (fun k x hx => GlobalTheory.BigRec.exists_rdU_ne_zero (T.U j T.σ₀) (fun i => (G.w i).1) hw k hx)
    ((hnz _ G.et het).2 T.σ₀ T.good_σ₀) ((hnz _ th1 hth1).2 T.σ₀ T.good_σ₀) ((hnz _ th2 hth2).2 T.σ₀ T.good_σ₀)
    (fun k => ⟨g0, (hnz _ g0 hg0).2 T.σ₀ T.good_σ₀ k⟩) (fun k => ?_) (fun k => ?_)
    (GlobalTheory.ExtraWeight.extra_weight_exists D T h j hj large₂ ka (GlobalTheory.RunIn.gamAt_of_lawsCore D _ h.toLawsCore) hrows hL hrn hjm
      hP.frd (sixteen_le_rdE_of_parA hP.hyp.1) (by exact_mod_cast lift_index_pow_four_le_degree hP.page))
  · refine ⟨thR wL, Real.exp (2 * (p14R wL * (DF wL : ℝ))) * lieFac (T.Q.Dw j) (xiR D) (wtA wL) ^ 2, hth,
      fun x hx => ?_⟩
    have h1 := hlow T.σ₀ T.good_σ₀ k x hx
    have hs : ∑ m, recNrm (T.U j T.σ₀) (xiR D) (wtA wL) wL.n (G.w m).1 k x ^ 2 =
        lieFac (T.Q.Dw j) (xiR D) (wtA wL) ^ 2 *
          ∑ m, ((T.U j T.σ₀).X k).pnorm (GlobalTheory.Shares.laR T j wL k) (rdR h j (G.w m) k) x ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [recNrm, mul_pow]; rfl
    have hpos : 0 < ∑ m, ((T.U j T.σ₀).X k).pnorm (GlobalTheory.Shares.laR T j wL k) (rdR h j (G.w m) k) x ^ 2 := by
      obtain ⟨m, hm⟩ := GlobalTheory.BigRec.exists_rdU_ne_zero (T.U j T.σ₀) (fun i => (G.w i).1) hw k hx
      exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
        ⟨m, Finset.mem_univ _, pow_pos (GlobalTheory.BigRec.pnorm_pos_of_ne_zero _ _ _ hx hm) 2⟩
    rw [hs] at h1
    have h2 := GlobalTheory.BigRec.exp_le_of_neg_log_sqrt_le (mul_pos (pow_pos (lieFac_pos _ _ _) 2) hpos) h1
    rw [← mul_assoc, ← mul_assoc] at h2
    exact h2
  · refine ⟨thR wL, _, hth, fun x hx => sq_le_of_mul_le_exp (lieFac_pos _ _ _) ?_ (harch T.σ₀ T.good_σ₀ k x hx)⟩
    exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _)

end GlobalTheory.RunJoin
end

