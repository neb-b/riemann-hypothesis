module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsOriginBoxValueExponentLe
section
open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem abs_lin_le (a a' u w M : ℤ) (hu : |u| ≤ M) (hw : |w| ≤ M) : |a * u - a' * w| ≤ M * (|a| + |a'|) := by
  calc |a * u - a' * w| ≤ |a * u| + |a' * w| := abs_sub _ _
    _ = |a| * |u| + |a'| * |w| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * M + |a'| * M := add_le_add (mul_le_mul_of_nonneg_left hu (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hw (abs_nonneg _))
    _ = M * (|a| + |a'|) := by ring

theorem abs_list_sum_le {α : Type*} (f : α → ℤ) (C : ℤ) :
    ∀ l : List α, (∀ b ∈ l, |f b| ≤ C) → |(l.map f).sum| ≤ l.length * C
  | [], _ => by simp
  | b :: l, h => by
    have h1 := h b (by simp)
    have h2 := abs_list_sum_le f C l fun x hx => h x (by simp [hx])
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add_one, add_mul, one_mul,
      add_comm ((l.length : ℤ) * C) C]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem abs_auxiliaryVectorUniformizerExponent_le (a a' : ℤ) {n : Type*} (c M : ℕ) (hc : c ≤ M) (y : n ⊕ Fin c) :
    |auxiliaryVectorUniformizerExponent a a' c y| ≤ (M : ℤ) * (|a| + |a'|) := by
  rcases y with x | p
  · simp only [auxiliaryVectorUniformizerExponent, abs_zero]; positivity
  · simp only [auxiliaryVectorUniformizerExponent]
    have hp := p.2
    apply abs_lin_le
    · rw [abs_of_nonneg (by omega)]; omega
    · rw [abs_of_nonneg (by omega)]; omega

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem abs_vtxExp_le (G : Grid k) (hs : 1 ≤ G.s) (a a' : ℤ) (j x : ℕ) (hx : x < G.rank (G.m, j)) :
    |vtxExp a a' (G.m - 1 - j) (topRank G j) x| ≤ (G.m : ℤ) * (|a| + |a'|) := by
  have key := topRank_add hs j
  unfold vtxExp
  split_ifs with h
  · apply abs_lin_le
    · rw [abs_of_nonneg (by omega)]; omega
    · rw [abs_of_nonneg (by omega)]; omega
  · simp only [abs_zero]; positivity

theorem abs_vtxDet_le (G : Grid k) (hs : 1 ≤ G.s) (a a' : ℤ) (N : ℕ)
    (hN : ∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) (X : ℕ × ℕ) (hX : X.2 ≤ G.m) :
    |vtxDet G a a' X| ≤ (N : ℤ) * ((G.m : ℤ) * (|a| + |a'|)) := by
  unfold vtxDet
  split_ifs with h
  · calc |∑ x : Fin (G.rank (G.m, X.2)), vtxExp a a' (G.m - 1 - X.2) (topRank G X.2) x|
          ≤ ∑ x : Fin (G.rank (G.m, X.2)), |vtxExp a a' (G.m - 1 - X.2) (topRank G X.2) x| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : Fin (G.rank (G.m, X.2)), (G.m : ℤ) * (|a| + |a'|) :=
            Finset.sum_le_sum fun x _ => abs_vtxExp_le G hs a a' X.2 x x.2
      _ = (G.rank (G.m, X.2) : ℤ) * ((G.m : ℤ) * (|a| + |a'|)) := by simp
      _ ≤ (N : ℤ) * ((G.m : ℤ) * (|a| + |a'|)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hN _ _ le_rfl hX
  · simp only [abs_zero]; positivity

theorem mem_oppositePath_bound {m : ℕ} {b : Edge} (hb : b ∈ oppositePath m) :
    b.src.1 ≤ m ∧ b.src.2 ≤ m ∧ b.tgt.1 ≤ m ∧ b.tgt.2 ≤ m := by
  simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
  rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · simp only [Edge.src, Edge.tgt]; omega
  · simp only [Edge.src, Edge.tgt]; omega

theorem length_oppositePath (m : ℕ) : (oppositePath m).length = 2 * m := by
  simp [oppositePath]; ring

theorem abs_pathSum_le (G : Grid k) (hs : 1 ≤ G.s) (a a' : ℤ) (N : ℕ)
    (hN : ∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) :
    |((oppositePath G.m).map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum|
      ≤ ((2 * G.m : ℕ) : ℤ) * (2 * ((N : ℤ) * ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|))))) := by
  rw [← length_oppositePath]
  apply abs_list_sum_le
  intro b hb
  obtain ⟨h1, h2, h3, h4⟩ := mem_oppositePath_bound hb
  have e1 := abs_vtxDet_le G hs a a' N hN b.src h2
  have e2 := abs_vtxDet_le G hs a a' N hN b.tgt h4
  have r1 : ((G.rank b.tgt : ℕ) : ℤ) ≤ N := by exact_mod_cast hN _ _ h3 h4
  have r2 : ((G.rank b.src : ℕ) : ℤ) ≤ N := by exact_mod_cast hN _ _ h1 h2
  have hC : 0 ≤ (N : ℤ) * ((G.m : ℤ) * (|a| + |a'|)) := by positivity
  calc |vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src|
        ≤ |vtxDet G a a' b.src * G.rank b.tgt| + |vtxDet G a a' b.tgt * G.rank b.src| := abs_sub _ _
    _ = |vtxDet G a a' b.src| * G.rank b.tgt + |vtxDet G a a' b.tgt| * G.rank b.src := by
        rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
    _ ≤ ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|))) * N + ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|))) * N :=
        add_le_add (mul_le_mul e1 r1 (by positivity) hC) (mul_le_mul e2 r2 (by positivity) hC)
    _ = 2 * ((N : ℤ) * ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|)))) := by ring

theorem abs_boxExp_le (G : Grid k) (a a' : ℤ) (j : Fin (G.m - 1))
    (v : StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j))) :
    |boxExp G a a' j v| ≤ (2 * (G.m : ℤ) + 1) * (|a| + |a'|) := by
  have hj := j.2
  have e1 := abs_auxiliaryVectorUniformizerExponent_le a a' (G.m - 2 - j + 1) G.m (by omega) v.1.2
  have e2 := abs_auxiliaryVectorUniformizerExponent_le a a' (G.m - 2 - j) G.m (by omega) v.1.1
  unfold boxExp
  have ha : |a| ≤ |a| + |a'| := le_add_of_nonneg_right (abs_nonneg _)
  calc |a - auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) v.1.2 + auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) v.1.1|
        ≤ |a - auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) v.1.2| + |auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) v.1.1| := abs_add_le _ _
    _ ≤ |a| + |auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) v.1.2| + |auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) v.1.1| := by
        gcongr; exact abs_sub _ _
    _ ≤ (|a| + |a'|) + (G.m : ℤ) * (|a| + |a'|) + (G.m : ℤ) * (|a| + |a'|) := by gcongr
    _ = (2 * (G.m : ℤ) + 1) * (|a| + |a'|) := by ring

open Classical in
theorem card_stepVar_le (G : Grid k) (hs : 1 ≤ G.s) (N : ℕ)
    (hN : ∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) (j : Fin (G.m - 1)) :
    Fintype.card (StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j))) ≤ N * N := by
  have hj := j.2
  have k0 := topRank_add hs j
  have k1 := topRank_add hs ((j : ℕ) + 1)
  have n0 := hN G.m j le_rfl (by omega)
  have n1 := hN G.m (j + 1) le_rfl (by omega)
  refine (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans ?_
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  exact Nat.mul_le_mul (by omega) (by omega)

open Classical in
theorem abs_boxSum_le (G : Grid k) (hs : 1 ≤ G.s) (a a' : ℤ) (N : ℕ)
    (hN : ∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) :
    |∑ j, ∑ v, boxExp G a a' j v| ≤ ((G.m - 1 : ℕ) : ℤ) * ((N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|))) := by
  have hC : 0 ≤ (2 * (G.m : ℤ) + 1) * (|a| + |a'|) := by positivity
  calc |∑ j, ∑ v, boxExp G a a' j v| ≤ ∑ j, |∑ v, boxExp G a a' j v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (G.m - 1), (N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        calc |∑ v, boxExp G a a' j v| ≤ ∑ v, |boxExp G a a' j v| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _v : StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j)),
                (2 * (G.m : ℤ) + 1) * (|a| + |a'|) := Finset.sum_le_sum fun v _ => abs_boxExp_le G a a' j v
          _ = (Fintype.card (StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j))) : ℤ) *
                ((2 * (G.m : ℤ) + 1) * (|a| + |a'|)) := by simp
          _ ≤ (N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|)) := by
                apply mul_le_mul_of_nonneg_right _ hC
                exact_mod_cast card_stepVar_le G hs N hN j
    _ = ((G.m - 1 : ℕ) : ℤ) * ((N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|))) := by simp

theorem abs_expo_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (G : Grid k), 1 ≤ G.s → ∀ (a a' : ℤ) (N : ℕ), (∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) →
      |expo G a a'| ≤ 8 * ((G.m : ℤ) ^ 3 * (N : ℤ) ^ 2 * (|a| + |a'|)) := by
  intro k _ _ _ _ G hs a a' N hN
  classical
  have hP := abs_pathSum_le G hs a a' N hN
  have hB := abs_boxSum_le G hs a a' N hN
  have hpoly : 4 * (G.m : ℤ) ^ 2 + 2 * ((G.m - 1 : ℕ) : ℤ) * (2 * (G.m : ℤ) + 1) ≤ 8 * (G.m : ℤ) ^ 3 := by
    rcases Nat.eq_zero_or_pos G.m with h | h
    · simp [h]
    · have h1 : ((G.m - 1 : ℕ) : ℤ) = (G.m : ℤ) - 1 := by push_cast [Nat.cast_sub h]; ring
      have h2 : (1 : ℤ) ≤ G.m := by exact_mod_cast h
      rw [h1]; nlinarith
  have hT : 0 ≤ (N : ℤ) ^ 2 * (|a| + |a'|) := by positivity
  unfold expo
  calc _ ≤ |((oppositePath G.m).map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum|
          + |2 * ∑ j, ∑ v, boxExp G a a' j v| := abs_sub _ _
    _ = |((oppositePath G.m).map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum|
          + 2 * |∑ j, ∑ v, boxExp G a a' j v| := by rw [abs_mul]; norm_num
    _ ≤ ((2 * G.m : ℕ) : ℤ) * (2 * ((N : ℤ) * ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|))))) +
          2 * (((G.m - 1 : ℕ) : ℤ) * ((N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|)))) := by gcongr
    _ = (4 * (G.m : ℤ) ^ 2 + 2 * ((G.m - 1 : ℕ) : ℤ) * (2 * (G.m : ℤ) + 1)) * ((N : ℤ) ^ 2 * (|a| + |a'|)) := by
          push_cast; ring
    _ ≤ 8 * (G.m : ℤ) ^ 3 * ((N : ℤ) ^ 2 * (|a| + |a'|)) := mul_le_mul_of_nonneg_right hpoly hT
    _ = 8 * ((G.m : ℤ) ^ 3 * (N : ℤ) ^ 2 * (|a| + |a'|)) := by ring

end GlobalTheory.OriginBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicProbabilityEqNormalisedFundamentalSets
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section
namespace GlobalTheory.LevGeo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem adelicProb_mul_volFund : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → (∑ k, muF ((U σ).X k) (x0 k) (FF k)) ≠ 0 ∧ (∑ k, muF ((U σ).X k) (x0 k) (FF k)) ≠ ⊤ ∧ ∀ Φ : ∀ k, Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞, (∀ k, Measurable (Φ k)) → (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, Φ k (lact γ x) = Φ k x) → (∀ k, ∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, Φ k (rmul x b) = Φ k x) → (∫⁻ q, Φ (dict σ q.out).1 (dict σ q.out).2 ∂(muQ1 (D.sp.W j))) * ∑ k, muF ((U σ).X k) (x0 k) (FF k) = ∑ k, ∫⁻ z in FF k, Φ k (cpt ((U σ).X k) (x0 k) z) ∂(muF ((U σ).X k) (x0 k)) := by
  intro D j H Dw l Xo c U dict hL σ hσ x0 FF hFF
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D (D.sp.W j) (D.sp.W_sig j)
  have hvp := Formalism.L2.Pj.volPair_isVolPair (D.sp.W j) hP
  haveI : (Formalism.L2.Pj.volPair (D.sp.W j)).1.IsHaarMeasure := hvp.1.1
  have h0 : (Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2 ≠ 0 :=
    Formalism.L2.Pj.muQ_univ (D.sp.W j) ▸ hV.1
  have h1 : (Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2 ≠ ⊤ :=
    Formalism.L2.Pj.muQ_univ (D.sp.W j) ▸ hV.2
  obtain ⟨Kf, th, hr, hK, hth, hd, hu⟩ := hL.dictU σ hσ
  have hU := hL.unf σ hσ
  have hΨ : ∀ k k', ((U σ).X k).Ψ = ((U σ).X k').Ψ ∧ ((U σ).X k).p0 = ((U σ).X k').p0 := fun k k' =>
    ⟨Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k').2 τ).symm, (hU.2.1 k).1.trans (hU.2.1 k').1.symm⟩
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨κ, hκ0, hκ1, hI⟩ := GlobalTheory.PeterssonCompare.lintegral_adelic (D.sp.W j) (U σ).X (dict σ) hM hth hd hK hu hΨ
    _ hvp.2 h0 h1
  set k0 := (dict σ 1).1
  obtain ⟨κ2, h20, h21, hH⟩ := _root_.GlobalTheory.FlagQuotHaar.quotInt_eq_const_mul D.R.r Dw.q ((U σ).X k0).Ψ.card
  have hQ : ∀ k (F : Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞), Measurable F →
      (∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, F (lact γ x) = F x) →
      (∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, F (rmul x b) = F x) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt ((U σ).X k) F = κ2 * ∫⁻ z in FF k, F (cpt ((U σ).X k) (x0 k) z) ∂(muF ((U σ).X k) (x0 k)) :=
    fun k F hF hΓ hB => hH D.host.E ((U σ).X k) (hU.2.1 k).1 (by rw [(hΨ k k0).1]) (x0 k) (FF k) F (hFF k).1 (hFF k).2
      hF hΓ hB
  have key : ∀ F : ∀ k, Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞, (∀ k, Measurable (F k)) →
      (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, F k (lact γ x) = F k x) →
      (∀ k, ∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, F k (rmul x b) = F k x) →
      ∫⁻ q, F (dict σ q.out).1 (dict σ q.out).2 ∂(muQ1 (D.sp.W j)) =
        ((Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2)⁻¹ *
          (κ * ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt ((U σ).X k) (F k)) := by
    intro F hF hΓ hB
    obtain ⟨h2, h3⟩ := hI F hF hΓ hB
    have hout : ∀ g, F (dict σ (Formalism.L2.Pj.autMk (D.sp.W j) g).out).1 (dict σ (Formalism.L2.Pj.autMk (D.sp.W j) g).out).2 =
        F (dict σ g).1 (dict σ g).2 := by
      intro g
      have h4 : g * (Formalism.L2.Pj.autMk (D.sp.W j) g).out⁻¹ ∈ GQ (D.sp.W j) :=
        QuotientGroup.rightRel_apply.1 (Quotient.mk_out g)
      obtain ⟨γ, hγ, e⟩ := hd.1 _ h4 (Formalism.L2.Pj.autMk (D.sp.W j) g).out
      rw [inv_mul_cancel_right] at e
      rw [e]
      exact (hΓ _ γ hγ _ (hd.2.2.2.1 _)).symm
    have hq : Measurable fun q : Formalism.L2.Pj.AutQ (D.sp.W j) => F (dict σ q.out).1 (dict σ q.out).2 := by
      rw [measurable_from_quotient]
      have : ((fun q : Formalism.L2.Pj.AutQ (D.sp.W j) => F (dict σ q.out).1 (dict σ q.out).2) ∘ Quotient.mk'') =
          fun g => F (dict σ g).1 (dict σ g).2 := funext hout
      rw [this]
      exact h2
    have h5 : ∫⁻ q, F (dict σ q.out).1 (dict σ q.out).2 ∂(Formalism.L2.Pj.muQ (D.sp.W j)) =
        κ * ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt ((U σ).X k) (F k) := by
      rw [Formalism.L2.Pj.muQ, lintegral_map hq (Formalism.L2.Pj.autMk_measurable (D.sp.W j))]
      simp only [hout]
      exact h3
    rw [Formalism.L2.Pj.muQ1, if_pos (show Formalism.L2.Pj.muQ (D.sp.W j) Set.univ ≠ 0 ∧ Formalism.L2.Pj.muQ (D.sp.W j) Set.univ ≠ ⊤
      from hV), lintegral_smul_measure, h5, Formalism.L2.Pj.muQ_univ, smul_eq_mul]
  have e1 := key (fun _ _ => 1) (fun _ => measurable_const) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
  rw [Finset.sum_congr rfl fun k _ => hQ k (fun _ => 1) measurable_const (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl),
    ← Finset.mul_sum] at e1
  simp only [setLIntegral_one, lintegral_const, measure_univ, mul_one, one_mul, Measure.restrict_apply_univ] at e1
  have hv0 : ((Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 h1
  refine ⟨fun hS => ?_, fun hS => ?_, fun Φ hΦ hΓ hB => ?_⟩
  · rw [hS, mul_zero, mul_zero, mul_zero] at e1
    exact one_ne_zero e1
  · rw [hS, ENNReal.mul_top h20, ENNReal.mul_top hκ0, ENNReal.mul_top hv0] at e1
    exact ENNReal.one_ne_top e1
  · rw [key Φ hΦ hΓ hB, Finset.sum_congr rfl fun k _ => hQ k (Φ k) (hΦ k) (hΓ k) (hB k), ← Finset.mul_sum]
    calc _ = (∑ k, ∫⁻ z in FF k, Φ k (cpt ((U σ).X k) (x0 k) z) ∂(muF ((U σ).X k) (x0 k))) *
          (((Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2)⁻¹ *
            (κ * (κ2 * ∑ k, muF ((U σ).X k) (x0 k) (FF k)))) := by ring
      _ = _ := by rw [← e1, mul_one]

end GlobalTheory.LevGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

namespace GlobalTheory.SchrLoc

open GlobalTheory.VacAny

theorem eq_atPlace_of_at {F : Type} [Field F] [NumberField F] {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {z : AF F}
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z) :
    z = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v z) := by
  have h1 := hz (1 - GlobalTheory.EmbChart.atPlace v 1)
    (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1
  conv_lhs => rw [h1]
  rw [GlobalTheory.EmbChart.atPlace_mul_right, one_mul]

theorem schr_tens_of_at : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.1 i)) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.2 i)) → ∀ (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ),
    (∀ x z : κ → AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z → r (x + z) = r x) →
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) φ r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v)
        (GlobalTheory.WeilM.schr (GlobalTheory.VacAny.psiV ψ v) (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i), fun i => GlobalTheory.AdelicU.evFin F v (w.2 i)) φ) r := by
  intro F _ _ ψ v κ _ w h1 h2 φ r hr
  have at_pi {z : κ → AF F} (h : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (z i)) :
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z :=
    fun u hu => funext fun i => h i u hu
  have at_mul_left (a : AF F) {b : AF F} (hb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) b) :
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (a * b) := fun u hu => by
    rw [smul_eq_mul, mul_left_comm, show u * b = 0 from hb u hu, mul_zero]
  have at_add {a b : AF F} (ha : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) a) (hb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) b) :
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (a + b) := fun u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]
  have at_sum {ι : Type} (s : Finset ι) {f : ι → AF F} (h : ∀ i ∈ s, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (f i)) :
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (∑ i ∈ s, f i) := by
    induction s using Finset.induction_on with
    | empty => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact at_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
  have evFin_invOf_two : GlobalTheory.AdelicU.evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
    refine (invOf_eq_right_inv ?_).symm
    have h : GlobalTheory.AdelicU.evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
    rwa [map_mul, map_ofNat] at h
  funext x
  have hr' : r (x + w.1) = r x := hr x w.1 (at_pi h1)
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) :=
    at_add (at_sum _ fun i _ => at_mul_left _ (h2 i))
      (at_mul_left _ (at_sum _ fun i _ => at_mul_left _ (h2 i)))
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
  rw [hr', eq_atPlace_of_at hz, ← psiV_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_add (f := _), map_mul, map_sum, evFin_invOf_two, Pi.add_apply]
  rw [show (fun i => GlobalTheory.AdelicU.evFin F v (x i) + GlobalTheory.AdelicU.evFin F v (w.1 i)) =
    (fun i => GlobalTheory.AdelicU.evFin F v (x i)) + (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i)) from rfl]
  ring

end GlobalTheory.SchrLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedAtLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TwistRam

theorem not_unrAt_alpha_div_beta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.E)), P ∈ L.Q t →
      P.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  intro D T L sc G μ₀ hL t i j w P hP hu hS
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have hchi : (G.ch.chiH (D.R.m - i)).UnrAt w := G.ch.unr _ hm.1 hm.2 w hS
  have hmu : (L.C.mu0 j).UnrAt w := (L.C.isMu0 j).unr _ fun k hk => hS (by
    have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
      rw [map_natCast]; exact hk
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have hxi : ¬ (L.xiH t).UnrAt w := by
    refine (hL.Q_ram t w).2 ?_
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (P := P) (Q := w) hu.symm with h | h
    · exact Or.inl (h ▸ hP)
    · exact Or.inr ⟨P, hP, GlobalTheory.GoodPrimes.isConjPl_iff.2 h⟩
  have e0 : alpha G t i j / beta G i j = G.nu t i (j + 1) := mul_div_mul_right_eq_div _ _ _
  rw [e0, GlobalTheory.LFun.unrAt_iff_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL)]
  intro hn
  apply hxi
  have e : L.xiH t = GlobalTheory.FunObj.SqNum.nuH G t i j * G.ch.chiH (D.R.m - i) / L.C.mu0 j := by
    rw [GlobalTheory.FunObj.SqNum.nuH, div_mul_cancel, mul_div_cancel_left]
  rw [e, div_eq_mul_inv]
  exact (hn.mul hchi).mul hmu.inv

end GlobalTheory.TwistRam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedFirst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FunObj.SqNum

theorem not_unrAt_alpha_div_beta_over_S₁ : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∈ S1 D →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  intro D T L sc G μ₀ hL t i j w hw
  have e : alpha G t i j / beta G i j = G.nu t i ((j : ℕ) + 1) := by
    simp only [alpha, beta, GridData.nu]
    exact mul_div_mul_right_eq_div _ _ _
  rw [e, GlobalTheory.LFun.unrAt_iff_of_chrEq (chrEq_nu (G := G) (t := t) (i := i) (j := j) hL) w]
  intro hu
  have hi1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have hi2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  refine (G.ch.lev1 _ hi1 hi2 w hw).2 fun x hx h1 => ?_
  have a1 := (L.C.isMu0 j).tame w x hx h1
  have a2 := hL.xi_tame t w x hx h1
  have a3 := hu x hx
  change ((L.C.mu0 j).loc w x * (L.xiH t).loc w x) *
    ((G.ch.chiH (D.R.m - i)).loc w x)⁻¹ = 1 at a3
  rw [a1, a2, one_mul, one_mul] at a3
  exact inv_eq_one.1 a3

end GlobalTheory.FunObj.SqNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Dets
section
set_option autoImplicit false

noncomputable section

open NumberField

namespace GlobalTheory.IdxTensor

def dets (F : Type) [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F)) : Submodule (𝓞 F) F :=
  Submodule.span (𝓞 F) {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ L) ∧ d = (Matrix.of y).det}

end GlobalTheory.IdxTensor

end
end

