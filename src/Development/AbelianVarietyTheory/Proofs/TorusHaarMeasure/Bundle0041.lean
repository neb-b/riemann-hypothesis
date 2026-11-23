module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.CountAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeadingProductsIndependentModuloDeepProducts
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunWeightDom

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.BddMulProd
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares GlobalTheory.UpTie
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.UpTie.LeadCount

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.UpTie.LeadCount.bdd_mul_pow (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {la L : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hP : X.IsBddSec la P) (hQ : X.IsBddSec L Q) (k : ℕ) : X.IsBddSec (la + k • L) (P * Q ^ k) := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    rw [succ_nsmul, ← add_assoc, pow_succ, ← mul_assoc]
    exact _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_mul X ih hQ


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.UpTie.LeadCount.bdd_mul_prod {n : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {la L : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hP : X.IsBddSec la P) {s : Fin n → _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hs : ∀ k, X.IsBddSec L (s k)) (α : Fin n → ℕ)
    (t : Finset (Fin n)) : X.IsBddSec (la + (∑ k ∈ t, α k) • L) (P * (∏ k ∈ t, s k ^ α k)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hP
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, add_comm (α a), add_smul, ← add_assoc,
      mul_comm (s a ^ α a), ← mul_assoc]
    exact _root_.GlobalTheory.UpTie.LeadCount.bdd_mul_pow X ih (hs a) (α a)

end GlobalTheory.UpTie.LeadCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RunWeightDominantAndGapsDefiniteCase
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.RunWeightDomDef


open GlobalTheory.RunWeightDom in
theorem run_weight_dom_definite : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → j = D.R.m → 8 ≤ D.R.r → ∀ k : (T.U j T.σ₀).Comp, ((T.U j T.σ₀).X k).p0 = 0 ∧ IsStrictDom ((T.U j T.σ₀).X k) (laR T j wL k) ∧ ∀ (τ : ((T.U j T.σ₀).X k).Ψ) (a b : Fin D.R.r), (b : ℕ) = a + 1 → (laR T j wF k - kapW ((T.U j T.σ₀).X k) - WeightFamilies.dimY D j • laR T j wL k) τ b + 2 * (laR T j wL k τ a - laR T j wL k τ b) ≤ (laR T j wF k - kapW ((T.U j T.σ₀).X k) - WeightFamilies.dimY D j • laR T j wL k) τ a := by
  intro D T h j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP hjm _ k
  obtain ⟨-, hS, -, -, -⟩ := hP
  obtain ⟨-, g1, g2, h4, -, h6, h7, -, -, -, -, -, -, -, hL, hF, -, -, -, h40, h21, -⟩ := hS
  obtain ⟨-, -, -, -, -, hp0, -, tt, hla⟩ := GlobalTheory.Shares.WtDic.weights_dictionary D T h j hj k
  have hk := D.R.m_add_three_le_k
  have hj1 := hj.1
  have hp : 0 < (D.R.sigW j).1 := by show 0 < D.R.k + j - 1; omega
  have hq : (D.R.sigW j).2 = 0 := by show D.R.m - j = 0; omega
  have hpq : (D.R.sigW j).1 + 0 = D.R.r := by
    show D.R.k + j - 1 + 0 = D.R.k + D.R.m - 1; omega
  have hz : ((T.U j T.σ₀).X k).p0 = 0 := hp0.trans hq
  have hTp : ((Tp D j Tn : ℕ) : ℤ) = (Tn : ℤ) + (WeightFamilies.dimY D j : ℤ) + 2 := by unfold Tp; push_cast; ring
  have h40' : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ Tn := by exact_mod_cast h40
  have h21' : ((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r ≤ Tn := by exact_mod_cast h21
  have hn : (nW : ℤ) = 2 * ((wL.n / 2 : ℕ) : ℤ) := by
    have := hL.1
    obtain ⟨c, hc⟩ := wL.n_even
    omega
  have key := fun τ : ((T.U j T.σ₀).X k).Ψ => by
    have bP := block hp (ka.aP (tt τ)) (wL.aP (tt τ)) (wF.aP (tt τ)) Tn (WeightFamilies.dimY D j) D.R.r
      (((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r) (Int.natCast_nonneg _) (Int.natCast_nonneg _) h40' h21'
      (fun i hi => by have := g1 (tt τ) i hi; push_cast at this; rwa [hTp] at this)
      (fun i hi => by
        have h1 : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aP (tt τ) i : ℝ) := by have := h6 (tt τ) i hi; linarith
        exact_mod_cast h1)
      (fun i => by have := hL.2.1 (tt τ) i; rwa [hTp, sub_sub] at this) (hF.2.1 (tt τ))
    rw [hn] at bP
    exact row hpq Tn (WeightFamilies.dimY D j) ((wL.n / 2 : ℕ) : ℤ) ((wF.n / 2 : ℕ) : ℤ) (Int.natCast_nonneg _)
      (Int.natCast_nonneg _) _ (fun _ => 2 * (Tn : ℤ)) _ (fun _ => ((WeightFamilies.dimY D j : ℤ) + 2) * (2 * (Tn : ℤ)))
      (laR T j wL k τ) (laR T j wF k τ) (Int.natCast_nonneg _)
      (fun a => by rw [hla, hz, if_pos (Nat.zero_le _), if_pos (Nat.zero_le _)])
      (fun a => by rw [hla, hz, if_pos (Nat.zero_le _), if_pos (Nat.zero_le _)])
      bP.1 bP.2.1 bP.2.2.1 bP.2.2.2
      (fun i hi => absurd hi (by omega)) (fun i hi => absurd hi (by omega)) (by omega) (by simp)
  refine ⟨hz, fun τ => ?_, fun τ a b hab => ?_⟩
  · obtain ⟨-, k2, -, -, -⟩ := key τ
    exact ⟨fun a b _ hb => absurd hb (by omega), fun a b _ hab => k2 a b (Nat.zero_le _) hab,
      fun a b ha _ => absurd ha (by omega)⟩
  · obtain ⟨-, -, k3, -, -⟩ := key τ
    simp only [Pi.sub_apply, nsmul_eq_mul, ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW]
    exact k3 a b hab (by omega)

end GlobalTheory.RunWeightDomDef
end

