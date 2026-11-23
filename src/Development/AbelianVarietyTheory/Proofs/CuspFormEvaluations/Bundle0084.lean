module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0074
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0082
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyUnimodular
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyLinear
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0079
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormFamiliesComplexCombinationOfReadings
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem rdOnto_rec : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) , LawsSh T → GamAt T.toCore → 0 < badN D → (∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0) → ∀ u : WeightFamilies.Wt D j, 8 * D.R.f * D.R.r + 4 ≤ u.n → LastPos (T.Q.Dw j) (wtA u) → RdOnto h j u := by
  intro hCI D T h j hj hSh hGam hbad hX u hu hLast f hf
  have hcu : ∀ g ∈ T.sh j u, ∃ F : (recB h.toLawsCore).Cusp j u, F.1 = g := by
    intro g hg
    refine ⟨⟨g, ?_⟩, rfl⟩
    have hC := hSh.shCusp j hj (wtA u) u.n (dom_wtA u) hLast (dom_wtA u) hLast hg
    unfold cutR
    exact Submodule.mem_inf.2 ⟨hC, (Submodule.mem_iInf _).2 fun hn => absurd hj hn⟩
  have hspan := _root_.GlobalTheory.Dict.holSub0_le_span_short_rec hCI D T h.toLawsCore.toLawsM hSh hGam hbad hX j hj u hu
  classical
  let f0 := fun (k : (T.U j T.σ₀).Comp) (x : Frame ((T.U j T.σ₀).X k).Ψ D.R.r) =>
    if x ∈ ((T.U j T.σ₀).X k).dom then f k x else 0
  have hf0 : f0 ∈ GlobalTheory.Dict.holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA u) u.n) := by
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · apply Submodule.subset_span
      intro k
      refine (GlobalTheory.DomCongr.bddSec_cusp_congr _ _ _ _ (f k) (f0 k) ?_).2 (hf k)
      intro x hx
      simp [f0, hx]
    · intro k x hx
      simp [f0, hx]
  obtain ⟨m, a, g, hg⟩ := Submodule.mem_span_set'.1 (hspan hf0)
  have hpre : ∀ i, ∃ F : (recB h.toLawsCore).Cusp j u, rdU (T.U j T.σ₀) F.1 = (g i).1 := by
    intro i
    obtain ⟨p, hp, hpg⟩ := (g i).2
    obtain ⟨F, rfl⟩ := hcu p hp
    exact ⟨F, hpg⟩
  choose F hF using hpre
  refine ⟨m, a, F, fun _ => Set.mem_univ _, ?_⟩
  intro k x hx
  have hfx : f k x = f0 k x := by simp [f0, hx]
  rw [hfx, ← hg]
  simp only [rdR, hF, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.Shares
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIntegralAuxiliaryCuspFormsSupBound
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ThetaIntegralWeights

theorem auxiliaryWeights_last_entry_pos {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {large₂ : SizeData₂ D} {H : KHyp}
    {C2 A2 CR CT : ℝ} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    (hP : FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0) :
    (∀ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2 → w2.LastPos) ∧ ∀ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW → w1.LastPos := by
  obtain ⟨-, hS, -, -, -⟩ := hP
  obtain ⟨-, -, -, h4, -, h6, -, -, -, -, -, -, -, -, hL, hF, -, -, -, h40, hc, -⟩ := hS
  obtain ⟨-, hLP, -⟩ := hL
  obtain ⟨-, hFP, -⟩ := hF

  have key : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 →
      ((Tn : ℤ) + WeightFamilies.dimY D j + 2 ≤ wL.aP τ i) ∧
        (ka.aP τ i : ℤ) + 1 ≤ ((Tn : ℤ) + WeightFamilies.dimY D j + 4) * wL.aP τ i := by
    intro τ i hi
    have hg := hLP τ i
    have hlt : ¬ (i.1 + 1 < (D.R.sigW j).1) := by omega
    simp only [gapZ, hlt, dif_neg, if_neg, not_false_eq_true] at hg
    have ha : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aP τ i : ℝ) := by
      have := h6 τ i hi
      linarith
    have ha' : 2 * (Tn : ℤ) ^ 2 ≤ (ka.aP τ i : ℤ) := by exact_mod_cast ha
    have k := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.weight_floor_inequalities (ka.aP τ i : ℤ) (wL.aP τ i : ℤ) (WeightFamilies.dimY D j : ℤ)
      (((WeightFamilies.dimY D j : ℤ) + 2) * nW) (2 * (D.R.r : ℤ)) Tn (Tp D j Tn : ℤ)
      (by simp only [Tp]; push_cast; ring) (by positivity) (by exact_mod_cast h40)
      (by exact_mod_cast hc) ha' (by rw [hg])
    simp only [Tp] at k
    push_cast at k
    exact k
  constructor
  · intro w2 hw2 τ i hi
    obtain ⟨-, h2P, -⟩ := hw2
    have e := h2P τ i
    have f := hFP τ i
    obtain ⟨k1, k2⟩ := key τ i hi
    have e' : (w2.aP τ i : ℤ) + wF.aP τ i = ((WeightFamilies.dimY D j : ℤ) + 4) * wL.aP τ i := by exact_mod_cast e
    have : (1 : ℤ) ≤ w2.aP τ i := by nlinarith
    exact_mod_cast this
  · intro w1 hw1 τ i hi
    obtain ⟨-, h1P, -⟩ := hw1
    obtain ⟨k1, -⟩ := key τ i hi
    have : (1 : ℤ) ≤ w1.aP τ i := by rw [h1P τ i]; push_cast; omega
    exact_mod_cast this

theorem familyHypothesesI4_recPJ_of_supBound_thInt : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → 16 ≤ D.R.f → (∀ w2, IsG2 wL wF w2 → ThInt (recPJ h j hj) hinj EX w2) → (j < D.R.m → ∀ w1, IsDoubledWeightWithShift wL w1 nW → ThInt (recPJ h j hj) hinj EX w1) → FamilyHypotheses.I4 large₂ (recPJ h j hj) wL wF nW := by
  intro hCI D T h hG hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP hR hf hT2 hT1
  have hj1 : 1 ≤ j := hj.1
  obtain ⟨hL2, -, -, hlam, hdim, -⟩ :=
    GlobalTheory.page_two_le_L_and_signs D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP hR
  have hdimR : (1 : ℝ) ≤ WeightFamilies.dimY D j := by exact_mod_cast hdim hj1
  obtain ⟨-, -, hw2, hw1⟩ :=
    GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hj1 hP
  obtain ⟨hW2, hW1⟩ :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.theta_weight_bounds D T h large₂ H C2 A2 CR CT j hj ka wL wF Tn nP nW h0 hP
  have hLast := auxiliaryWeights_last_entry_pos hP
  obtain ⟨⟨w2, hg2⟩, -⟩ :=
    GlobalTheory.AuxiliaryWeightsExistence.exists_auxiliaryWeights_at_runWeights D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP
  obtain ⟨hr2, -, hq2⟩ := hW2 w2 hg2
  obtain ⟨hdf2, hn2, hsz2⟩ := hw2 w2 hg2
  have hpr2 := GlobalTheory.pageRows_of_le D large₂ j ka w2 (by linarith) hdf2 hn2 hR

  set lN := Real.log (Fintype.card (T.U j T.σ₀).Comp) with hlN
  have hN0 : 0 ≤ lN := Real.log_natCast_nonneg _
  have hN : lN ≤ 41 * Zb D large₂ ^ 2 :=
    _root_.GlobalTheory.RunIn.log_card_comp_le D T h large₂ j hj w2 hpr2 hL2 hr2 hf T.σ₀ (Formalism.L2.Pj.Core.good_σ₀ _)
  have hZ : 0 ≤ Zb D large₂ := by
    unfold Zb
    exact mul_nonneg (by positivity) (by linarith)
  have hA : 0 ≤ 400 * Zb D large₂ + lamStar D := by linarith
  have hs : 1 ≤ wL.size := WeightFamilies.Wt.one_le_size wL
  have hPI : WeightAlgebra.PI4 D j (400 * Zb D large₂) lN * (WeightFamilies.dimY D j : ℝ) =
      5 * (400 * Zb D large₂ + lamStar D) * WeightFamilies.dimY D j + 2 * lN := by
    have : (WeightFamilies.dimY D j : ℝ) ≠ 0 := by linarith
    unfold WeightAlgebra.PI4
    field_simp
  have hAs : 0 ≤ (400 * Zb D large₂ + lamStar D) * wL.size := mul_nonneg hA (by linarith)
  refine ⟨400 * Zb D large₂, lN, by nlinarith, by nlinarith, ?_, ?_⟩
  · intro hjm
    obtain ⟨⟨w1, hg1⟩⟩ := (⟨(GlobalTheory.AuxiliaryWeightsExistence.exists_auxiliaryWeights_at_runWeights D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF
      Tn nP nW h0 hP).2⟩ : Nonempty _)
    obtain ⟨hr1, -, hq1⟩ := hW1 hjm w1 hg1
    obtain ⟨hdf1, hn1, hsz1⟩ := hw1 w1 hg1
    have hpr1 := GlobalTheory.pageRows_of_le D large₂ j ka w1 (by linarith) hdf1 hn1 hR
    obtain ⟨th, hth, hnz, hb⟩ :=
      _root_.GlobalTheory.ThetaComb.exists_integral_theta_nonzero_on_components hCI D T h hG large₂ j hj w1 hpr1 hL2 hr1 (hLast.2 w1 hg1) hq1 hinj EX (hT1 hjm w1 hg1)
    refine ⟨w1, hg1, th, hth, hnz, fun σ => ?_⟩
    have e : 2 * WeightAlgebra.PI4 D j (400 * Zb D large₂) lN * (WeightFamilies.dimY D j : ℝ) * wL.size =
        2 * (5 * (400 * Zb D large₂ + lamStar D) * WeightFamilies.dimY D j + 2 * lN) * wL.size := by
      rw [← hPI]; ring
    rw [e]
    nlinarith [hb σ, mul_le_mul_of_nonneg_left hsz1 hA, mul_nonneg hAs (sub_nonneg.2 hdimR),
      mul_nonneg hN0 (sub_nonneg.2 hs)]
  · obtain ⟨th, hth, hnz, hb⟩ :=
      _root_.GlobalTheory.ThetaComb.exists_integral_theta_nonzero_on_components hCI D T h hG large₂ j hj w2 hpr2 hL2 hr2 (hLast.1 w2 hg2) hq2 hinj EX (hT2 w2 hg2)
    refine ⟨w2, hg2, th, hth, hnz, fun σ => ?_⟩
    have e : WeightAlgebra.PI4 D j (400 * Zb D large₂) lN * (WeightFamilies.dimY D j : ℝ) * wL.size =
        (5 * (400 * Zb D large₂ + lamStar D) * WeightFamilies.dimY D j + 2 * lN) * wL.size := by
      rw [← hPI]
    rw [e]
    nlinarith [hb σ, mul_le_mul_of_nonneg_left hsz2 hA, mul_nonneg hAs (sub_nonneg.2 hdimR),
      mul_nonneg hN0 (sub_nonneg.2 hs)]

end GlobalTheory.ThetaIntegralWeights
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IntegralityBoundOfFamilyContainingScaledThetaRul
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem totalDegree_eq_sum_rows {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ harmA c a n) (h0 : P ≠ 0) (hh : P.IsHomogeneous P.totalDegree) :
    P.totalDegree = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
  classical
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.2 h0
  have hr := hP.1.2.2 m hm
  have h1 := hh (MvPolynomial.mem_support_iff.1 hm)
  have h2 : m.degree = P.totalDegree := by rw [Finsupp.degree_eq_weight_one]; exact h1
  rw [← h2, Finsupp.degree_eq_sum]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hr τ i

theorem lieFac_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (x : ℝ) (hx : 0 < x)
    (a : (E →+* ℂ) × ℕ → ℕ) (d : ℕ) (hd : d = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)) :
    lieFac Dw x a ^ 2 = ((2 * Real.pi * x)⁻¹) ^ d := by
  have hp : 0 < 2 * Real.pi * x := by positivity
  have hd' : (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) = d := by rw [hd]; push_cast; rfl
  unfold lieFac
  rw [hd', ← Real.exp_nat_mul, ← Real.exp_log (inv_pos.2 hp), ← Real.exp_nat_mul, Real.log_inv]
  congr 1
  push_cast
  ring

theorem i2iAt_of_containsTh : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (xR : ℝ) (nab : NabV Xo c), IsNab Xo c nab → (∀ σ, GoodEmb c σ → IsUnf (U σ) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x)) ∧ ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xR) → ∀ α : 𝓞 E, α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P₁ : MvPolynomial (LtN Dw n) c.F), Dom a n → P₁ ∈ harmA c a n → IsBlockProd P₁ → ∀ s : c.F, (∀ σ : c.F →+* ℂ, (l.M : ℝ) ^ P₁.totalDegree ≤ ‖σ s‖ ^ 2) → ∀ (N : ℕ) (wR : Fin (N + 1) → Rul Xo c), (∀ i, wR i ∈ sec Xo c a n) → ContainsTh Xo c nab s P₁ wR → ∀ (R0 : ℝ) (m : ℕ), RunOK E r P₁.totalDegree l.M R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ tableLineDegreeFive cc : ℝ, p14 E r n m ≤ tableLineDegreeFive → 8100 * Real.pi * n * (m : ℝ) ^ 4 * (I2.dstar (E := E) m : ℝ) ^ 4 * I2.RR (E := E) / l.M ≤ cc → I2AtFramePoints U xR wR (a, n) (I2.th (E := E) l.M R0) tableLineDegreeFive P₁.totalDegree cc := by
  intro hCI E _ _ _ H Dw l Xo c _ r U xR nab hnab hU α hα hMb a n P₁ hdom hP hbp s hs N wR hw hct R0 m hrun hm
    tableLineDegreeFive cc hP14 hcc σ hσ k x hx
  classical
  obtain ⟨hUn, hFT, hxi⟩ := hU σ hσ
  obtain ⟨b, -, hbd, hbo, -, hphi, hpn⟩ := exists_ortho_frame E r ((U σ).X k) x hx
  obtain ⟨T, Pr, hTr, hq, hPm, hph, hbound⟩ := GlobalTheory.T.unfoldedThetaRule_archimedeanValue_bound hCI E H Dw l Xo c σ r (U σ) k ⟨_, hbd⟩ xR nab hnab hσ hUn
    (hFT k _) hbo (hxi k) α hα hMb a n P₁ hP hbp R0 m hrun hm
  obtain ⟨h0, hh, -⟩ := _root_.GlobalTheory.BlockRen.blockProd_rename E H Dw n c.F σ P₁ hbp Dw.mult id (fun _ => le_rfl) Function.injective_id
  have hdeg := totalDegree_eq_sum_rows c a n P₁ hP h0 hh
  have hxR : 0 < xR := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← hxi k τ]
    exact norm_pos_iff.2 ((map_ne_zero τ).2 ((U σ).X k).ξ0_ne)
  have hM : (0 : ℝ) < l.M := by
    have := Pr.hq
    rw [hq] at this
    exact_mod_cast this
  obtain ⟨jb, hjb, hf⟩ := hct
  choose f hf1 hf2 using hf
  haveI : Finite (LevQ Dw l) := (GlobalTheory.card_levQ E H Dw l).1
  haveI : Fintype (Fin n → LevQ Dw l) := Fintype.ofFinite _
  have hb := hbound f hf1
  rw [finsum_eq_sum_of_fintype] at hb
  have hrec : ∀ j, recNrm (U σ) xR a n (wR j) k x =
      lieFac Dw xR a * ‖rdU (U σ) (wR j) k (FD.rmul x b)‖ := fun j => by
    unfold recNrm
    rw [hpn _ _ (hUn.2.2.2.2.1 a n hdom (wR j) (hw j) k)]
  have hval : ∀ q, rdU (U σ) (wR (jb q)) k (FD.rmul x b) =
      σ s * toC (evR Xo c (f q) ((U σ).un k ⟨_, hbd⟩)) := fun q => by
    have e : wR (jb q) = s • f q := by
      funext p y
      rw [hf2 q p y]
      exact (Algebra.smul_def s (f q p y)).symm
    rw [e, map_smulₛₗ]
    show σ s * rdU (U σ) (f q) k (FD.rmul x b) = _
    congr 1
    exact dif_pos hbd
  have hkey : (Real.pi⁻¹) ^ P₁.totalDegree * Pr.Jbound n ≤ ∑ j, recNrm (U σ) xR a n (wR j) k x ^ 2 := by
    have hl := lieFac_sq Dw xR hxR a _ hdeg
    have hL : (0 : ℝ) ≤ ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree := by positivity
    calc (Real.pi⁻¹) ^ P₁.totalDegree * Pr.Jbound n
        = ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree * ((l.M : ℝ) ^ P₁.totalDegree *
            ((2 * xR / l.M) ^ P₁.totalDegree * Pr.Jbound n)) := by
          rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← mul_pow, ← mul_pow]
          congr 2
          field_simp
      _ ≤ ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree * ((l.M : ℝ) ^ P₁.totalDegree *
            ∑ q, ‖toC (evR Xo c (f q) ((U σ).un k ⟨_, hbd⟩))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (by positivity)) hL
      _ ≤ ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree * (‖σ s‖ ^ 2 *
            ∑ q, ‖toC (evR Xo c (f q) ((U σ).un k ⟨_, hbd⟩))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hs σ)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hL
      _ = ∑ q, recNrm (U σ) xR a n (wR (jb q)) k x ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [hrec, hval, mul_pow, hl, norm_mul, mul_pow]
      _ = ∑ j ∈ Finset.univ.image jb, recNrm (U σ) xR a n (wR j) k x ^ 2 :=
          (Finset.sum_image (f := fun j => recNrm (U σ) xR a n (wR j) k x ^ 2) fun _ _ _ _ h => hjb h).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  have hfin := neg_log_sqrt_le_of_jbound E T P₁.totalDegree n Pr _ tableLineDegreeFive cc hkey (by rw [hTr, hPm]; exact hP14)
    (by rw [hPm, hq]; exact hcc)
  rw [hph] at hfin
  rw [← hphi]
  exact hfin

end GlobalTheory.AnVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortGeneratorMemSpanSmallSupNormShortGenerators
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem fg_of_trivAt_even {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) {bad : ℕ}
    (h2 : 2 ∣ bad) (h : Λ.TrivAt bad) : Λ.La.FG := by
  obtain ⟨k, hk, hle, -⟩ := h
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hk
    omega
  have hstd : (stdLat E n).FG := by
    unfold stdLat
    exact Submodule.fg_pi fun _ => Submodule.fg_unit 1
  have hkO : (k : 𝓞 E) ≠ 0 := by exact_mod_cast hk0
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 E) (Fin n → E) (k : 𝓞 E)) :=
    LinearMap.lsmul_injective hkO
  refine Submodule.fg_of_fg_map_injective _ hinj ?_
  have hN := isNoetherian_of_fg_of_noetherian _ hstd
  refine isNoetherian_submodule.1 hN _ ?_
  rintro _ ⟨v, hv, rfl⟩
  exact hle (Submodule.smul_mem_smul (Ideal.subset_span rfl) hv)

theorem sh_mem_span_small : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ g ∈ T.sh j w, g ∈ Submodule.span T.Q.c.F {g' : T.R j | g' ∈ T.sh j w ∧ ∀ σ, Real.log (T.Ns j w σ g') ≤ 400 * Zb D large₂ * w.size} := by
  intro hCI D T h hG large₂ j hj w hP hL hrn hlp hS hA g hg
  obtain ⟨hgs, Λ, N, x0, P, hU, hT1, hT2, hLev, hAdm, hPh, hR⟩ := hg
  obtain ⟨-, -, -, -, -, hfd, -, hrd, hfr, hf1, -⟩ := _root_.GlobalTheory.HostClear.host_clear D large₂.sc.L hL hP.2.1 hP.2.2.1 hP.2.2.2.1
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := ((_root_.GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins).2.2.2.2.2.2 j hj).1
  have hfg : Λ.La.FG := fg_of_trivAt_even Λ (by
    unfold badN
    have h2 : 2 ∣ D.host.QS := (D.host.mem_small_iff.1 D.host.two_mem_small).2
    exact ((h2.mul_right _).mul_right _).mul_right _) hT1
  have hdf : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ (Formalism.MainNotions.WeightAlgebra.DF w : ℝ) := by
    exact_mod_cast ReciprocityTheory.ChartRestriction.G.PullbackSections.DF_wtA_le T j w
  have e : ((Formalism.MainNotions.WeightAlgebra.DF w : ℕ) : ℝ) = absA w := by
    unfold absA Formalism.MainNotions.WeightAlgebra.DF degP
    push_cast
    rfl
  obtain ⟨S, hS1, hS2, -⟩ := _root_.GlobalTheory.Harm.exists_short_harmL_family D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c w.n Λ hU hfg (hr ▸ hrn) (wtA w)
    large₂.sc.L hL hrd (by rw [hfd]; exact hP.2.2.2.2.1)
    ((Real.log_le_log (by positivity) (by linarith)).trans hP.2.2.2.2.2.2.2.1) hP.2.2.2.2.2.2.2.2
  obtain ⟨m, cf, Q, hsum⟩ := Submodule.mem_span_set'.1 (hS2 P hPh.1)
  have hQ : ∀ i, (Q i).1 ∈ harmL T.Q.c Λ (wtA w) := fun i => (hS1 _ (Q i).2).1
  choose gs hgs1 hgs2 using fun i =>
    (hS.shTot j hj (wtA w) w.n (dom_wtA w) Λ N x0 (Q i).1 hU hT1 hT2 hLev hAdm (hQ i)).2
  have hlin := _root_.GlobalTheory.ShortRuleLinear.shortRule_linear hCI D T h hS j hj w Λ N x0 hU hT2 hLev m cf (fun i => (Q i).1) g gs hQ hgs hgs1
    (by rw [hsum]; exact hR) hgs2
  rw [hlin]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨⟨hgs1 i, Λ, N, x0, (Q i).1, hU, hT1, hT2, hLev, hAdm, hQ i, hgs2 i⟩, fun σ => ?_⟩)
  have hL0 : 0 ≤ large₂.sc.L := by linarith
  have hA0 : 0 ≤ absA w := by rw [← e]; positivity
  have hb : Real.log (l1At σ (Q i).1) ≤ 140 * D.R.r * large₂.sc.L * absA w := by
    refine ((hS1 _ (Q i).2).2 σ).trans ?_
    rw [hr, ← e]
    exact mul_le_mul_of_nonneg_left hdf (by positivity)
  have hl1 : l1At σ (Q i).1 ≤ Real.exp (140 * D.R.r * large₂.sc.L * absA w) :=
    (Real.le_exp_log _).trans (Real.exp_le_exp.2 hb)
  have hsup := GlobalTheory.T.log_supNorm_shortThetaGenerator_le hCI D T h hG large₂ j hj w hP hL hrn (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w hlp) hS hA
    Λ N x0 (Q i).1 (gs i) hU hT1 hT2 hLev hAdm (hQ i) (hgs2 i) (hgs1 i) σ _ (by positivity) hl1
  exact hsup.trans (_root_.GlobalTheory.RunIn.sup_bounds_le_Gc D (recB h.toLawsCore) large₂ j w 0 hL (by omega)).1

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNetDimensionAndPointCountBoundStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.thetaNet_dimension_and_pointCount_bound : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → ∃ (Nt : NetNorms.NetData (recB h.toLawsCore) j ka) (σ₀ : (recB h.toLawsCore).KO →+* ℂ), NetNorms.NetMax Nt ∧ NetNorms.NetLeSup Nt ∧ NetNorms.NetPageG Nt large₂ 1041 3 ∧ NetNorms.NetInj Nt σ₀ ∧ Real.log (Fintype.card (Nt.NN σ₀) : ℝ) ≤ pdR large₂ ka ∧ DeepSubMul (recPJ h j hj) ∧ Real.log (Module.finrank (recB h.toLawsCore).KO ((recB h.toLawsCore).Cusp j ka) : ℝ) ≤ 1041 * Zb D large₂ ^ 3 ∧ ∀ del : ℕ, LatAt (recB h.toLawsCore) j ka → ShareRd (D := D) (j := j) Tn del ((recPJ h j hj).rk ka ((recB h.toLawsCore).Mlat j ka)) → Real.log del ≤ 1041 * Zb D large₂ ^ 3 := by
  exact @GlobalTheory.RunJoin.net_at_run
end

