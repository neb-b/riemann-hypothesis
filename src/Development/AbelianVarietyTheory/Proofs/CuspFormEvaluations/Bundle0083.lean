module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SumLeFinsumOfSurjectsOntoFinset
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NetDataExists
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SumLeFinsumOfSurjectsOntoFinsetStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedThetaRule_archimedeanValue_bound : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (xR : ℝ) (nab : NabV Xo c), IsNab Xo c nab → GoodEmb c σ → IsUnf U → FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x) → (U.X k).IsOrtho x.1 → (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = xR) → ∀ α : 𝓞 E, α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P₁ : MvPolynomial (LtN Dw n) c.F), P₁ ∈ harmA c a n → IsBlockProd P₁ → ∀ (R0 : ℝ) (m : ℕ), RunOK E r P₁.totalDegree l.M R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∃ (T : I2.PT E) (Pr : I2.Par T P₁.totalDegree), T.r = r ∧ Pr.q = l.M ∧ Pr.m = m ∧ Pr.ph = I2.phiFD (U.X k) (I2.th (E := E) l.M R0) x.1 ∧ ∀ f : (Fin n → LevQ Dw l) → Rul Xo c, (∀ q, IsThRule Xo c nab (fun b => levRep (q b)) P₁ (f q)) → (2 * xR / l.M) ^ P₁.totalDegree * Pr.Jbound n ≤ ∑ᶠ q, ‖toC (evR Xo c (f q) (U.un k x))‖ ^ 2 := by
  first | exact @GlobalTheory.ThetaLower.thetaRule_sum_lower | exact GlobalTheory.ThetaLower.thetaRule_sum_lower | (intros; apply GlobalTheory.ThetaLower.thetaRule_sum_lower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNetDimensionAndPointCountBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

theorem net_count_dim {D : D7} {B : WeightFamilies.Prov D} {j : ℕ} {ka : WeightFamilies.Wt D j} (Nt : NetNorms.NetData B j ka)
    (σ : B.KO →+* ℂ) (c : ℝ) (hM : NetNorms.NetMax Nt) (hS : NetNorms.NetSize Nt c) (hI : NetNorms.NetInj Nt σ) :
    Real.log (Fintype.card (Nt.NN σ) : ℝ) ≤ c ∧ ∀ n : ℕ, n ≤ Module.finrank B.KO (B.Cusp j ka) → Real.log n ≤ c := by
  have hlog16 : ∀ k : ℕ, Real.log (k : ℝ) ≤ Real.log (16 * (k : ℝ)) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      exact Real.log_le_log hk' (by linarith)
  have hfirst : Real.log (Fintype.card (Nt.NN σ) : ℝ) ≤ c := (hlog16 _).trans (hS σ)
  refine ⟨hfirst, ?_⟩
  intro n hn

  have hdim : Module.finrank B.KO (B.Cusp j ka) ≤ Fintype.card (Nt.NN σ) := by
    have hli := hI _ (Module.finBasis B.KO (B.Cusp j ka)) (Module.finBasis B.KO (B.Cusp j ka)).linearIndependent
    have hle := hli.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using hle
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hc : 0 ≤ Real.log (16 * (Fintype.card (Nt.NN σ) : ℝ)) := by
      rcases Nat.eq_zero_or_pos (Fintype.card (Nt.NN σ)) with h0 | h0
      · rw [h0]
        simp
      · apply Real.log_nonneg
        have : (1 : ℝ) ≤ Fintype.card (Nt.NN σ) := by exact_mod_cast h0
        linarith
    simp only [Nat.cast_zero, Real.log_zero]
    linarith [hS σ]
  · calc Real.log (n : ℝ) ≤ Real.log (Fintype.card (Nt.NN σ) : ℝ) := by
          apply Real.log_le_log (by exact_mod_cast hnpos)
          exact_mod_cast hn.trans hdim
      _ ≤ c := hfirst

theorem le_finrank_of_shareRd {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (ka : WeightFamilies.Wt D j)
    (N : Submodule (𝓞 B.KO) (B.Cusp j ka)) (Tn del : ℕ) (hT : WeightFamilies.dimY D j + 1 ≤ Tn)
    (hR : ShareRd (D := D) (j := j) Tn del (X.rk ka N)) : del ≤ Module.finrank B.KO (B.Cusp j ka) := by
  have hpos : 0 < Nat.choose (Tn - 1) (WeightFamilies.dimY D j) := Nat.choose_pos (by omega)
  have hc : (1 : ℝ) ≤ (Nat.choose (Tn - 1) (WeightFamilies.dimY D j) : ℝ) := by exact_mod_cast hpos
  have hR' : (Nat.choose (Tn - 1) (WeightFamilies.dimY D j) : ℝ) * del ≤ (X.rk ka N : ℝ) := hR
  have hdel0 : (0 : ℝ) ≤ del := by positivity
  have hdel : (del : ℝ) ≤ (X.rk ka N : ℝ) := by nlinarith

  have hrk : X.rk ka N ≤ Module.finrank B.KO (B.Cusp j ka) := Submodule.finrank_le _
  have hdel' : del ≤ X.rk ka N := by exact_mod_cast hdel
  exact hdel'.trans hrk


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem net_at_run : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → ∃ (Nt : NetNorms.NetData (recB h.toLawsCore) j ka) (σ₀ : (recB h.toLawsCore).KO →+* ℂ), NetNorms.NetMax Nt ∧ NetNorms.NetLeSup Nt ∧ NetNorms.NetPageG Nt large₂ 1041 3 ∧ NetNorms.NetInj Nt σ₀ ∧ Real.log (Fintype.card (Nt.NN σ₀) : ℝ) ≤ pdR large₂ ka ∧ DeepSubMul (recPJ h j hj) ∧ Real.log (Module.finrank (recB h.toLawsCore).KO ((recB h.toLawsCore).Cusp j ka) : ℝ) ≤ 1041 * Zb D large₂ ^ 3 ∧ ∀ del : ℕ, LatAt (recB h.toLawsCore) j ka → ShareRd (D := D) (j := j) Tn del ((recPJ h j hj).rk ka ((recB h.toLawsCore).Mlat j ka)) → Real.log del ≤ 1041 * Zb D large₂ ^ 3 := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP
  obtain ⟨hyp, page, _tie, _p13, _frd, r8, _df, ck⟩ := hP
  obtain ⟨hrows, hf⟩ := GlobalTheory.pageRows_of_pageAt D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hyp page ck
  obtain ⟨hParA, hSetC, -, -, -⟩ := hyp
  obtain ⟨_Q, _PT, hSz, -, -⟩ := page
  obtain ⟨hL2, -⟩ := GlobalTheory.EtaAn.page_rows D large₂ H.CA hParA hSz
  obtain ⟨hkn, -, -, -, -, -, -, -, -, hnP, -, -, -, hnV, -, -, -, -, -, h40, -⟩ := hSetC
  have hfr : D.R.r ≤ D.R.f * D.R.r := Nat.le_mul_of_pos_left _ (by omega)
  have hr : D.R.r ≤ ka.n := by
    rw [hkn, hnV]
    have : D.R.f * D.R.r ≤ 8 * D.R.f * D.R.r := by
      rw [Nat.mul_assoc]
      omega
    omega
  have hZ : 1 ≤ Zb D large₂ := by
    have hf' : (16 : ℝ) ≤ D.R.f := by exact_mod_cast hf
    have hr' : (8 : ℝ) ≤ D.R.r := by exact_mod_cast r8
    have hfr' : (128 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    show 1 ≤ (D.R.f : ℝ) * D.R.r * large₂.sc.L
    nlinarith
  obtain ⟨Nt, hM, hLe, hS, hI⟩ := GlobalTheory.RunIn.NetAtRecord.netData_exists D T h
    (GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore) large₂ j hj ka hrows hL2 hr hf
  let σ₀ : (recB h.toLawsCore).KO →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ)).toRingHom
  obtain ⟨hcnt, hdim⟩ := net_count_dim Nt σ₀ _ hM hS (hI σ₀)
  have hpg := GlobalTheory.page_relation_deg_three D large₂ j ka 1041 3 le_rfl le_rfl hZ
  refine ⟨Nt, σ₀, hM, hLe, fun σ => (hS σ).trans hpg, hI σ₀, hcnt.trans hpg,
    (GlobalTheory.deepSubMul_rec_all D T h j hj).1, hdim _ le_rfl, ?_⟩
  intro del _hLat hR
  exact hdim _ (le_finrank_of_shareRd (recPJ h j hj) ka _ Tn del (by omega) hR)

end GlobalTheory.RunJoin
end

