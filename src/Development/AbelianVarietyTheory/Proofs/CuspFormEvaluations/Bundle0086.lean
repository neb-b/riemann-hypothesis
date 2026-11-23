module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LowerBoundAtFramesFamilyWithScaledThetaRules
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegreeInterpolationBounds

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem totalDegree_eq_DF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : Coeff l) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) (h0 : P ≠ 0) :
    P.totalDegree = Formalism.L2.Pj.DF Dw a := by
  have key : ∀ m ∈ P.support, (m.sum fun _ e => e) = Formalism.L2.Pj.DF Dw a := by
    intro m hm
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Formalism.L2.Pj.DF]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP.1.2.2 m hm τ i
  obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 h0)
  apply le_antisymm
  · exact Finset.sup_le fun m' hm' => (key m' hm').le
  · exact (key m hm) ▸ MvPolynomial.le_totalDegree hm

theorem pow_le_sq_of_log {M x : ℝ} {d : ℕ} (hM : 1 < M) (hd : 1 ≤ d) (hx : 0 ≤ x)
    (h : (d : ℝ) / 2 * Real.log M ≤ Real.log x) : M ^ d ≤ x ^ 2 := by
  have hl : 0 < Real.log M := Real.log_pos hM
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx0 : 0 < x := by
    rcases hx.eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero] at h
      nlinarith
    · exact h0
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  linarith

theorem i2iAt_record : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (_EX : ErrX D) (j : ℕ) (hj : InR D j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (S : Scal (recB h.toLawsCore)) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → EtaleWeightGaps.PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW S wL → ∀ (P₁ : MvPolynomial (LtN (T.Q.Dw j) wL.n) T.Q.c.F), P₁ ∈ harmA T.Q.c (wtA wL) wL.n → IsBlockProd P₁ → ∀ (N : ℕ) (w : Fin (N + 1) → (recB h.toLawsCore).Cusp j wL), ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) ((S.sW : (recB h.toLawsCore).KO) : T.Q.c.F) P₁ (fun k => ((w k).1 : T.R j)) → ∀ tableLineDegreeFive : ℝ, p14 D.host.E D.R.r wL.n D.R.m ≤ tableLineDegreeFive → I2AtFramePoints (T.U j) (xiR D) (fun k => ((w k).1 : T.R j)) (wtA wL, wL.n) (I2.th (E := D.host.E) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL)))) tableLineDegreeFive (WeightAlgebra.DF wL) (cc D large₂ C2 A2 CR wL) := by
  intro hCI D T h EX j hj K Ch Ah Cq Aq S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hHP hTie hPage hSupp P₁ hP hB N w hC
    tableLineDegreeFive hP14
  obtain ⟨inst, hnab⟩ := h.nabPin j hj
  obtain ⟨α, hα1, hα2⟩ := GlobalTheory.RunIn.half_level_generator_norm D T h EX
  obtain ⟨hrun, hcc, -, -⟩ := GlobalTheory.T.thetaRunParameters_at_typePrimes_product D _ _ j (recPJ h j hj) K Ch Ah Cq Aq S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0
    hHP hTie hPage hSupp
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hP0 : P₁ ≠ 0 := fun e => GlobalTheory.BlockThInhab.not_isBlockProd_zero (T.Q.Dw j) wL.n T.Q.c.F (e ▸ hB)
  have hdeg : P₁.totalDegree = WeightAlgebra.DF wL :=
    (totalDegree_eq_DF T.Q.c hP hP0).trans (GlobalTheory.WeightExponents.weight_exponents D T.Q h.pins j hj wL).1
  have hq : (T.Q.Dw j).q ≤ D.R.m := by
    rw [(h.pins.2.2.2 j hj).2.1]
    exact Nat.sub_le _ _
  have hs : ∀ σ : T.Q.c.F →+* ℂ,
      (T.Q.l.M : ℝ) ^ P₁.totalDegree ≤ ‖σ ((S.sW : (recB h.toLawsCore).KO) : T.Q.c.F)‖ ^ 2 := by
    intro σ
    have h3 : (3 : ℝ) ≤ T.Q.l.M := by exact_mod_cast T.Q.l.three_le
    refine pow_le_sq_of_log (by linarith) (by rw [hdeg]; have := hSupp.2.2.2.2; omega) (norm_nonneg _) ?_
    rw [hdeg, hM, Nat.cast_mul]
    exact hSupp.2.1 σ
  have key := GlobalTheory.T.integralityBound_of_family_containing_scaled_thetaRules hCI D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (xiR D) (T.nab j) hnab
    (fun σ hσ => ⟨h.unf j hj σ hσ, h.unTest j hj σ hσ, h.xiAbs j hj σ hσ⟩) α hα1 hα2 (wtA wL) wL.n P₁ (dom_wtA wL) hP hB
    _ hs N (fun k => ((w k).1 : T.R j)) (fun k => cusp_le_sec _ _ _ _ _ (cutR_le T.C j wL (w k).2)) hC
    (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL))) D.R.m (by rw [hdeg, hM]; exact hrun) (Or.inr hq) tableLineDegreeFive
    (cc D large₂ C2 A2 CR wL) hP14 (by rw [hM]; exact hcc)
  rw [hdeg, hM] at key
  exact key

end GlobalTheory.DegreeInterpolationBounds
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunScalarsNonzeroBoundedSupBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem scalB_rec : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → LawsSh T → (∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1) → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.OwnPr D p → FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) wF → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ((recPJ h j hj).wF0 wL wF) → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ka → ScalB large₂ (recPJ h j hj) H.C1 H.A1 (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn := by
  intro hCI D T h hGam hSh hA hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp hHP hRows hSpF hSpF0 hSpK
  obtain ⟨-, hSet, -, -, -⟩ := id hHP
  obtain ⟨hkaN, -, -, -, -, -, -, -, -, -, -, -, -, hnV, hIsL, hIsF, -, -, -, -, -, h40, -, -, -, -⟩ := hSet
  have hLn : wL.n = nW := hIsL.1
  have hkn : ka.n = nP + Tn * nW := hkaN.trans hnV
  have hp0 : 0 < p := by
    rcases hp with rfl | rfl
    · exact D.host.pde_prime.pos
    · exact D.host.pde'_prime.pos
  have hj1 : 1 ≤ j := hj.1
  obtain ⟨hL2, -, hr6, hlam, -, -⟩ := GlobalTheory.page_two_le_L_and_signs D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hHP hRows
  have hwb := GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hj1 hHP
  have hsz := _root_.GlobalTheory.RunIn.scalOfP_size D (recB h.toLawsCore) hinj EX j p ka wL wF Tn nP nW hp0 (by omega) hLn hIsF hkn
  have hsW := _root_.GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D (recB h.toLawsCore) hinj EX j wL
  have hWeq := GlobalTheory.RunIn.sW_eq_sOf (recB h.toLawsCore) hinj EX p ka wL wF Tn
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  have hZ : 0 ≤ Zb D large₂ := by
    unfold Zb
    exact mul_nonneg (by positivity) (by linarith)

  have hW : ∀ w ∈ ({wL, wF, (recPJ h j hj).wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w ∧ D.R.r ≤ w.n ∧ w.LastPos := by
    intro w hw
    obtain ⟨hdf, hn, hr, hlast⟩ := hwb.1 w hw
    exact ⟨GlobalTheory.pageRows_of_le D large₂ j ka w (by linarith) hdf hn hRows, hr, hlast⟩

  have hShort : ∀ (w : WeightFamilies.Wt D j) (s : 𝓞 (recB h.toLawsCore).KO) (c : ℝ),
      w ∈ ({wL, wF, (recPJ h j hj).wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)) →
      ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) w → s ≠ 0 → 0 ≤ c →
      c ≤ 2 * (lamStar D + 2 * Real.log p) * w.size →
      (∀ σ : (recB h.toLawsCore).KO →+* ℂ, Real.log ‖σ (s : (recB h.toLawsCore).KO)‖ ≤ c) →
      ShortG (recPJ h j hj) w ((recPJ h j hj).Thc s w) (Gc large₂ (recB h.toLawsCore) (1009 * Zb D large₂) p * w.size) := by
    intro w s c hw hsp hs hc0 hc hsc
    obtain ⟨hRw, hrw, hlw⟩ := hW w hw
    have hn8 : 0 < w.n := by omega
    obtain ⟨Sh, hSh1, hSh2⟩ := GlobalTheory.RunIn.exists_short_family_small hCI D T h hGam large₂ j hj w hRw hL2 hrw hlw hSh (hA j hj w.n) hsp
    have hsize : 1 ≤ w.size := WeightFamilies.Wt.one_le_size w
    have key := _root_.GlobalTheory.RunIn.shortG_scaled D _ _ j (recPJ h j hj) w s Sh c (400 * Zb D large₂ * w.size) hs hc0
      (mul_nonneg (by linarith) (by linarith)) hsc hSh1 hSh2
    have hG := (_root_.GlobalTheory.RunIn.sup_bounds_le_Gc D (recB h.toLawsCore) large₂ j w p hL2 hn8).2.1
    unfold ShortG at key ⊢
    obtain ⟨S', hS'1, hS'2, hS'3⟩ := key
    exact ⟨S', hS'1, hS'2, fun g hg => (hS'3 g hg).trans (by nlinarith)⟩
  unfold ScalB
  refine ⟨hWeq ▸ hsW.1, hsz.1, hsz.2.1, hsz.2.2.1, fun σ => ?_, p, (Formalism.MainNotions.Gaps.FamilyHypotheses.ownPr_iff D p).1 hp,
    fun σ => hsz.2.2.2 σ, 1009 * Zb D large₂, le_rfl, ?_⟩
  · rw [hWeq]
    exact ⟨(hsW.2 σ).1, (hsW.2 σ).2.1⟩
  unfold S4
  have hsizeL : 1 ≤ wL.size := WeightFamilies.Wt.one_le_size wL
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨hRL, hrL, hlL⟩ := hW wL (by simp)
    have hnL : 0 < wL.n := by omega
    obtain ⟨N, w0, hspan, -, hsup⟩ := _root_.GlobalTheory.ThetaFamily.theta_family hCI D T h hGam large₂ j hj wL hRL hL2 hrL hlL
    have hG := (_root_.GlobalTheory.RunIn.sup_bounds_le_Gc D (recB h.toLawsCore) large₂ j wL p hL2 hnL).2.2
    have hdisc : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| := by
      rw [Real.log_abs]
      exact Real.log_intCast_nonneg _
    have hb : 0 ≤ 400 * Zb D large₂ * wL.size + 3 * D.R.f * D.R.r * wL.n * large₂.sc.L +
        5 * Real.log (Module.finrank ℚ (recB h.toLawsCore).KO) +
        Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| / Module.finrank ℚ (recB h.toLawsCore).KO + 2 := by
      have h1 : 0 ≤ Real.log (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) := Real.log_natCast_nonneg _
      have h2 : 0 ≤ (3 * D.R.f * D.R.r * wL.n : ℝ) * large₂.sc.L := mul_nonneg (by positivity) (by linarith)
      have h3 : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| / Module.finrank ℚ (recB h.toLawsCore).KO :=
        div_nonneg hdisc (by positivity)
      have h4 : 0 ≤ 400 * Zb D large₂ * wL.size := mul_nonneg (by linarith) (by linarith)
      linarith
    exact (GlobalTheory.ScaledGenerators.scaled_family D _ _ j (recPJ h j hj) ka wL wF _ N w0 _ _ _ 0
      (mul_nonneg (by linarith) (by linarith)) hb (fun σ => (hsz.2.2.2 σ).1) hspan hsup hG).1
  · have hsF : ∀ σ : (recB h.toLawsCore).KO →+* ℂ, Real.log ‖σ ((scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn).sF : (recB h.toLawsCore).KO)‖ ≤ (lamStar D + 2 * Real.log p) * wF.size :=
      fun σ => (hsz.2.2.2 σ).2.1
    exact hShort wF _ _ (by simp) hSpF hsz.1 (mul_nonneg (by linarith) (by linarith [WeightFamilies.Wt.one_le_size wF])) (by nlinarith [WeightFamilies.Wt.one_le_size wF]) hsF
  · exact hShort _ _ _ (by simp) hSpF0 hsz.2.1 (mul_nonneg (by linarith) (by linarith [WeightFamilies.Wt.one_le_size ((recPJ h j hj).wF0 wL wF)])) le_rfl (fun σ => (hsz.2.2.2 σ).2.2.1)
  · exact hShort ka _ _ (by simp) hSpK hsz.2.2.1 (mul_nonneg (by linarith) (by linarith [WeightFamilies.Wt.one_le_size ka])) le_rfl (fun σ => (hsz.2.2.2 σ).2.2.2)

end GlobalTheory.RunIn
end

