module

public import Mathlib
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0074
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0047

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasurableDomCellLogNormChart
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open GroundTheory.Heights₂.Heights (chartLift chartLiftDom contDiff_chartLift chartLift_blockNonzero segre_chartLift
  chartWeight_of_coord)

section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {m : ℕ}

theorem eval_chartSection (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (s : MRingOver ℂ ι)
    (x : Fin m → ℂ) : MvPolynomial.eval x (chartSection σ i s) = MvPolynomial.eval (chartLift σ i x) s := by
  induction s using MvPolynomial.induction_on with
  | C c => simp [chartSection]
  | add p q hp hq =>
    have : chartSection σ i (p + q) = chartSection σ i p + chartSection σ i q := by
      simp [chartSection]
    rw [this, map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p q hp =>
    have : chartSection σ i (p * X q) =
        chartSection σ i p * X (σ.symm (Function.update i q.1 q.2)) := by
      simp [chartSection]
    rw [this, map_mul, map_mul, hp]
    simp [chartLift]

theorem mem_closedBall_of_lift_mem_domCell {S : Set ((Σ k, ι k) → ℂ)} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {x : Fin m → ℂ} (hx : x ∈ chartSet S σ i) (hd : chartLift σ i x ∈ domCell i) :
    x ∈ Metric.closedBall (0 : Fin m → ℂ) 1 := by
  obtain ⟨z, -, hzi, rfl⟩ := hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro a
  have h := hd (σ a)
  rw [segre_chartLift σ i z hzi, hzi, norm_one] at h
  exact h

theorem abs_log_div_le {t h c : ℝ} (ht : 0 ≤ t) (hh : 0 < h) (hc : |Real.log h| ≤ c) (hc0 : 0 ≤ c) :
    |Real.log (t / h)| ≤ |Real.log t| + c := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa using hc0
  · rw [Real.log_div ht.ne' hh.ne']
    exact (abs_sub _ _).trans (by gcongr)

end

theorem integrable_chartAbsDens_cellWeight : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (N : Fin e → HermLine ι)
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ)
    (J : Ideal (MvPolynomial (Fin m) ℂ)),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i →
    J ∈ chartComponents (conePts Q) σ i →
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ) →
    (∀ R C : ℝ, Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      ((Metric.closedBall 0 R).indicator fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + C)
      (chartPot σ i N))) →
    Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) (chartPot σ i N)) := by
  intro K _ _ ι _ Q e m σ i Ψ N A s a J hA _ _ hmeas hzero hJ hproj hint
  classical
  set T : Set (Fin m → ℂ) := Metric.closedBall 0 1 ∩ {x | x (σ.symm i) = 1} with hT
  have hTc : IsCompact T :=
    (isCompact_closedBall (0 : Fin m → ℂ) 1).inter_right
      (isClosed_eq (continuous_apply _) continuous_const)
  have hcont : ContinuousOn (fun x => Real.log (A.h (chartLift σ i x))) T := by
    have h1 : ContinuousOn (fun x => A.h (chartLift σ i x)) T :=
      hA.continuousOn.comp (contDiff_chartLift σ i (n := 0)).continuous.continuousOn
        fun x hx => chartLift_blockNonzero σ i hx.2
    exact h1.log fun x hx => (A.pos _ (chartLift_blockNonzero σ i hx.2)).ne'
  obtain ⟨C, hC⟩ := hTc.exists_bound_of_continuousOn hcont
  have hchart : ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J, x ∈ chartSet (conePts Q) σ i := by
    intro x hx
    rw [← hzero]
    intro q hq
    exact hx q ((mem_chartComponents.1 hJ).1.2 hq)
  have hcoord : ∀ x ∈ chartSet (conePts Q) σ i, x (σ.symm i) = 1 := by
    rintro _ ⟨z, -, hzi, rfl⟩
    simpa using hzi
  have hmeasW : Measurable (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) := by
    unfold chartWeight
    exact (hmeas.comp (contDiff_chartLift σ i (n := 0)).continuous.measurable).piecewise
      (GroundTheory.Heights₂.Heights.isOpen_chartLiftDom σ i).measurableSet measurable_const
  have hmeasD : Measurable (chartAbsDens J (chartProjMatrix σ Ψ)
      (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) (chartPot σ i N)) :=
    GroundTheory.Heights₂.Heights.SheetSumMeasurable.measurable_sheetSum hproj (fun a b => |a * b|)
      ((continuous_mul.comp continuous_id).abs.measurable) hmeasW _
  refine (hint 1 (max C 0)).mono' hmeasD.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (GroundTheory.Heights₂.Heights.chartAbsDens_nonneg _ _ _ _ _)]
  have key : ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J,
      |chartWeight σ i ((domCell i).indicator (absLogNorm A s)) x| ≤
        |(Metric.closedBall (0 : Fin m → ℂ) 1).indicator
          (fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + max C 0) x| := by
    intro x hx
    have hxc := hchart x hx
    have h1 := hcoord x hxc
    rw [chartWeight_of_coord _ h1]
    by_cases hd : chartLift σ i x ∈ domCell i
    · have hb := mem_closedBall_of_lift_mem_domCell hxc hd
      have hC' : |Real.log (A.h (chartLift σ i x))| ≤ max C 0 :=
        (hC x ⟨hb, h1⟩).trans (le_max_left _ _)
      have hnz := chartLift_blockNonzero σ i h1
      have habs : absLogNorm A s (chartLift σ i x) = |logNormC A s (chartLift σ i x)| := by
        simp only [absLogNorm]
        rw [if_pos hnz]
      rw [Set.indicator_of_mem hd, Set.indicator_of_mem hb, habs, abs_abs, logNormC,
        ← eval_chartSection]
      exact (abs_log_div_le (norm_nonneg _) (A.pos _ hnz) hC' (le_max_right _ _)).trans
        (le_abs_self _)
    · rw [Set.indicator_of_notMem hd, abs_zero]
      exact abs_nonneg _
  have h := GroundTheory.Heights₂.Heights.sheetSum_le_mul (J := J) (A := chartProjMatrix σ Ψ) (y := y)
    (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hproj y) 1
    (fun x t => |chartWeight σ i ((domCell i).indicator (absLogNorm A s)) x *
      ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i N k ∘ t) y|)
    (fun x t => |(Metric.closedBall (0 : Fin m → ℂ) 1).indicator
      (fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + max C 0) x *
      ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i N k ∘ t) y|)
    (fun x hx t _ => by
      rw [one_mul, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (key x hx.1) (abs_nonneg _))
  exact h.trans_eq (one_mul _)

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJLowerUniSwap
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.MatRead

theorem det_of_key {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (f : Fin m → ℕ) (hf : Function.Injective f)
    (h : ∀ i j, f i < f j → A i j = 0) : A.det = ∏ i, A i i := by
  rw [Matrix.det_apply, Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    obtain ⟨i, hi⟩ : ∃ i, f (σ i) < f i := by
      by_contra hne
      simp only [not_exists, not_lt] at hne
      apply hσ
      have hsum : ∑ i, f (σ i) = ∑ i, f i := Equiv.sum_comp σ f
      have heq := (Finset.sum_eq_sum_iff_of_le (fun i _ => hne i)).mp hsum.symm
      refine Equiv.ext (fun i => ?_)
      exact (hf (heq i (Finset.mem_univ i)).symm : σ i = i)
    have hz : ∏ j, A (σ j) j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (h _ _ hi)
    rw [hz, smul_zero]
  · intro h1
    exact absurd (Finset.mem_univ 1) h1

private theorem minor_col_lemma {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (hX : IsLowerUni X)
    (S I : Finset (Fin N)) (a b : Fin N) (hb : b ∈ S) (hIS : I.erase a = S.erase b)
    (hcol : ∀ d ∈ I, d ≠ a → X d b = 0) (k : ℕ) (hI : I.card = k) (hS : S.card = k)
    (p q : Fin k) (hp : I.orderEmbOfFin hI p = a) (hq : S.orderEmbOfFin hS q = b) :
    (X.submatrix (I.orderEmbOfFin hI) (S.orderEmbOfFin hS)).det = (-1) ^ ((p : ℕ) + (q : ℕ)) * X a b := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := Finset.card_pos.mpr ⟨b, hb⟩; omega⟩
  have hcol' : ∀ i, i ≠ p → X (I.orderEmbOfFin hI i) b = 0 := by
    intro i hi
    refine hcol _ (Finset.orderEmbOfFin_mem I hI i) (fun h1 => hi ?_)
    apply (I.orderEmbOfFin hI).injective
    rw [h1, hp]
  have hT : (S.erase b).card = n := by
    rw [Finset.card_erase_of_mem hb, hS, Nat.add_sub_cancel]
  have hg' : ⇑(S.orderEmbOfFin hS) ∘ q.succAbove = (S.erase b).orderEmbOfFin hT := by
    apply Finset.orderEmbOfFin_unique hT
    · intro x
      rw [Function.comp_apply, Finset.mem_erase]
      exact ⟨fun h1 => Fin.succAbove_ne q x ((S.orderEmbOfFin hS).injective (h1.trans hq.symm)),
        Finset.orderEmbOfFin_mem S hS _⟩
    · exact (S.orderEmbOfFin hS).strictMono.comp (Fin.strictMono_succAbove q)
  have hg : ⇑(I.orderEmbOfFin hI) ∘ p.succAbove = (S.erase b).orderEmbOfFin hT := by
    apply Finset.orderEmbOfFin_unique hT
    · intro x
      rw [Function.comp_apply, ← hIS, Finset.mem_erase]
      exact ⟨fun h1 => Fin.succAbove_ne p x ((I.orderEmbOfFin hI).injective (h1.trans hp.symm)),
        Finset.orderEmbOfFin_mem I hI _⟩
    · exact (I.orderEmbOfFin hI).strictMono.comp (Fin.strictMono_succAbove p)
  have hdetT : (X.submatrix ((S.erase b).orderEmbOfFin hT) ((S.erase b).orderEmbOfFin hT)).det = 1 := by
    rw [det_of_key _ (fun i => (((S.erase b).orderEmbOfFin hT i : Fin N) : ℕ)) ?_ ?_]
    · exact Finset.prod_eq_one (fun i _ => hX.1 _)
    · intro i j hij
      exact ((S.erase b).orderEmbOfFin hT).injective (Fin.ext hij)
    · intro i j hij
      exact hX.2 _ _ hij
  rw [Matrix.det_succ_column _ q, Finset.sum_eq_single p]
  · have e1 : (X.submatrix (I.orderEmbOfFin hI) (S.orderEmbOfFin hS)) p q = X a b := by
      rw [Matrix.submatrix_apply, hp, hq]
    rw [e1, Matrix.submatrix_submatrix, hg, hg', hdetT, mul_one]
  · intro i _ hi
    rw [Matrix.submatrix_apply, hq, hcol' i hi, mul_zero, zero_mul]
  · intro h1
    exact absurd (Finset.mem_univ p) h1

theorem exists_sign {N : ℕ} (S : Finset (Fin N)) (a b : Fin N) (ha : a ∉ S) (hb : b ∈ S) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ X : Matrix (Fin N) (Fin N) ℂ, IsLowerUni X → (∀ d ∈ S, d ≠ b → X d b = 0) →
      minorIJ X (insert a (S.erase b)) S = c * X a b := by
  have haS : a ∉ S.erase b := fun h1 => ha (Finset.mem_of_mem_erase h1)
  have hcard : (insert a (S.erase b)).card = S.card := by
    rw [Finset.card_insert_of_notMem haS, Finset.card_erase_of_mem hb]
    have := Finset.card_pos.mpr ⟨b, hb⟩
    omega
  obtain ⟨p, hp⟩ : ∃ p, (insert a (S.erase b)).orderEmbOfFin hcard p = a := by
    have h1 : a ∈ Set.range ((insert a (S.erase b)).orderEmbOfFin hcard) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_insert_self _ _
    exact h1
  obtain ⟨q, hq⟩ : ∃ q, S.orderEmbOfFin rfl q = b := by
    have h1 : b ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hb
    exact h1
  refine ⟨(-1) ^ ((p : ℕ) + (q : ℕ)), pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero), fun X hX hcol => ?_⟩
  rw [minorIJ, dite_eq_left hcard]
  refine minor_col_lemma X hX S _ a b hb (Finset.erase_insert haS) ?_ _ hcard rfl p q hp hq
  intro d hd hda
  rcases Finset.mem_insert.mp hd with h1 | h1
  · exact absurd h1 hda
  · exact hcol d (Finset.mem_of_mem_erase h1) (Finset.ne_of_mem_erase h1)

theorem minor_replace : ∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) (a b : Fin N), IsLowerUni X → a ∉ S → b ∈ S → b < a → (∀ c ∈ S, c ≠ b → X c b = 0) → minorIJ X (insert a (S.erase b)) S = pSgn S a b * X a b ∧ pSgn S a b ≠ 0 := by
  intro N X S a b hX ha hb hba hcol
  obtain ⟨c, hc0, hc⟩ := exists_sign S a b ha hb
  have hab : a ≠ b := (ne_of_lt hba).symm
  have hY : IsLowerUni (1 + Matrix.single a b (1 : ℂ)) := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply,
        if_neg (fun h1 => hab (h1.1.trans h1.2.symm)), add_zero]
    · rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hij), Matrix.single_apply,
        if_neg (fun h1 => lt_asymm hba (by rw [h1.1, h1.2]; exact hij)), add_zero]
  have hYcol : ∀ d ∈ S, d ≠ b → (1 + Matrix.single a b (1 : ℂ)) d b = 0 := by
    intro d hd hdb
    have hda : d ≠ a := fun h1 => ha (h1 ▸ hd)
    rw [Matrix.add_apply, Matrix.one_apply_ne hdb, Matrix.single_apply,
      if_neg (fun h1 => hda h1.1.symm), add_zero]
  have hp : pSgn S a b = c := by
    rw [pSgn, hc _ hY hYcol, Matrix.add_apply, Matrix.one_apply_ne hab, Matrix.single_apply,
      if_pos ⟨rfl, rfl⟩, zero_add, mul_one]
  rw [hp]
  exact ⟨hc X hX hcol, hc0⟩

end GlobalTheory.CompanionTheory.Ar.PB.PFl.MatRead
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PMatStepColsEntry
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep

theorem stepCols_subset_of_le {N j : ℕ} (hj : j ≤ N) {m i b x : Fin N} (hmi : m ≤ i)
    (hb : b ∈ stepCols N j m) (hb' : b ∈ stepCols N j i) (hx : x ∈ stepCols N j m) : x ∈ stepCols N j i := by
  have h1 := m.2
  have h2 := i.2
  have h3 := b.2
  have h4 := x.2
  have h5 : (m : ℕ) ≤ i := hmi
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hb hb' hx ⊢
  split_ifs at hb hb' hx ⊢ <;> omega

theorem pStep_reads (Ψ : Type) (N j : ℕ) (keep : Ψ × Fin N → Prop) (q : PIdx j keep) (hj : j ≤ N) :
    keep (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) ∧ IsProperStep N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧
      q.1.1.2.2 ∈ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧
      q.1.1.2.1 ∉ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧
      ∀ c : PIdx j keep → ℂ, pMat keep c q.1.1.1 q.1.1.2.1 q.1.1.2.2 = c q ∧
        ∀ x ∈ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2), x ≠ q.1.1.2.2 →
          pMat keep c q.1.1.1 x q.1.1.2.2 = 0 := by
  obtain ⟨⟨⟨τ, a, b⟩, hlt, hblk⟩, hsep⟩ := q
  obtain ⟨i, hk, hp, hb, ha⟩ := id hsep
  dsimp only at hk hp hb ha hlt hblk ⊢
  have hne : (pSteps j keep τ b).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hp, hb⟩⟩
  have hm : pStep j keep τ b ∈ pSteps j keep τ b := by
    unfold pStep
    rw [dite_eq_left hne]
    exact Finset.min'_mem _ _
  have hmin : ∀ i' ∈ pSteps j keep τ b, pStep j keep τ b ≤ i' := by
    intro i' hi'
    unfold pStep
    rw [dite_eq_left hne]
    exact Finset.min'_le _ _ hi'
  obtain ⟨hmk, hmp, hmb⟩ := (Finset.mem_filter.mp hm).2
  refine ⟨hmk, hmp, hmb, fun hx => ha (stepCols_subset_of_le hj (hmin i ?_) hmb hb hx), fun c => ⟨?_, ?_⟩⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hp, hb⟩
  · unfold pMat lowMat
    rw [dite_eq_left (⟨hlt, hblk⟩ : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j))]
    unfold cExt
    rw [dite_eq_left hsep]
  · intro x hx hxb
    unfold pMat lowMat
    by_cases hc : b < x ∧ ((x : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · rw [dite_eq_left hc]
      unfold cExt
      refine dif_neg ?_
      rintro ⟨i', hk', hp', hb', hx'⟩
      exact hx' (stepCols_subset_of_le hj
        (hmin i' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk', hp', hb'⟩)) hmb hb' hx)
    · rw [_root_.dite_eq_right hc, if_neg hxb]

end GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFunctionAnalyticOnChart
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_valAt_lift_family : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (s : Ω) (e n : ℕ) (Rb : AnLogRes (mCoordIdeal x) ⊤ n) (Un : Set (Fin e → ℂ)) (bp : (Fin e → ℂ) → Rb.X) (w₀ : Fin e → ℂ), IsOpen Un → w₀ ∈ Un → ContinuousOn bp Un → (∀ k, AnalyticOnNhd ℂ (Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (Rb.A.chart k).source)) → RegAt x (mCoordIdeal (Rb.lift (bp w₀) (bp w₀))) s → AnalyticAt ℂ (fun w => valAt x s (Rb.lift (bp w) (bp w))) w₀ := by
  intro K _ ι _ Ω _ x s e n Rb Un bp w₀ hUn hw₀ hbp hchart hreg
  obtain ⟨W', hW'o, hx₀W', hW'U, hW'holo⟩ :=
    GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_valAt K ι Ω x s n Rb.X Rb.A (Rb.U (bp w₀))
      (Rb.lift (bp w₀)) (bp w₀) (Rb.isOpen_U _) (Rb.mem_U _) (fun q => Rb.holo _ q)
      (fun y hy => Rb.mem _ y hy) hreg
  obtain ⟨j, hj⟩ := Rb.A.cover (bp w₀)
  have hg : AnalyticAt ℂ ((fun y => GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w₀) y)) ∘ (Rb.A.chart j).symm) ((Rb.A.chart j) (bp w₀)) := by
    apply hW'holo j
    refine ⟨(Rb.A.chart j).map_source hj, ?_⟩
    show (Rb.A.chart j).symm ((Rb.A.chart j) (bp w₀)) ∈ W'
    rw [(Rb.A.chart j).left_inv hj]
    exact hx₀W'
  have hf : AnalyticAt ℂ ((Rb.A.chart j) ∘ bp) w₀ := hchart j w₀ ⟨hw₀, hj⟩
  have hcomp : AnalyticAt ℂ (((fun y => GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w₀) y)) ∘ (Rb.A.chart j).symm) ∘ ((Rb.A.chart j) ∘ bp)) w₀ :=
    AnalyticAt.comp_of_eq (g := (fun y => GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w₀) y)) ∘ (Rb.A.chart j).symm) (f := (Rb.A.chart j) ∘ bp) hg hf rfl
  refine hcomp.congr ?_
  have hcont : ContinuousAt bp w₀ := hbp.continuousAt (hUn.mem_nhds hw₀)
  have hnhds : bp ⁻¹' ((Rb.A.chart j).source ∩ W') ∈ 𝓝 w₀ :=
    hcont.preimage_mem_nhds (((Rb.A.chart j).open_source.inter hW'o).mem_nhds ⟨hj, hx₀W'⟩)
  filter_upwards [hnhds] with w hw
  obtain ⟨hws, hwW⟩ := hw
  show GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w₀) ((Rb.A.chart j).symm ((Rb.A.chart j) (bp w)))) = GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w) (bp w))
  rw [(Rb.A.chart j).left_inv hws]
  exact (GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit K ι Ω x s _ _ (Rb.mem _ _ (Rb.mem_U _))
    (Rb.compat (bp w) (bp w₀) (bp w) ⟨Rb.mem_U _, hW'U hwW⟩)).symm

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.StepFactorNeZeroStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_factor_ne_zero : ∀ (N j : ℕ) (a i : Fin N) (h : Matrix (Fin N) (Fin N) ℂ), IsBlockDiag j h → h.det ≠ 0 → facOf N j a h i ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.facOf_ne_zero | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.facOf_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.facOf_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.UnipotentValueNeZero
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.UpsNe

theorem upsVal_ne_zero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n)  (l : Fin BM.q) (p : Ψ × Fin N) (b : BM.Rb.X), b ∈ BM.O l → M.blk p = none → upsVal BM l p b ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM l p b hb hp
  obtain ⟨hne, hreg, hreg'⟩ := (BM.good l b hb).2.2 p hp
  exact ValNe.valAt_ne_zero_of_regAt_inv _ _ M.Ω M.x _ _ (BM.Rb.mem b b (BM.Rb.mem_U b)) hne hreg hreg'

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.UpsNe
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueConstantOnOrbitStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_constant_on_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (s : Ω) (z z' : (Σ k, ι k) → ℂ), z ∈ mcPts (mCoordIdeal x) → SameOrbit z z' → valAt x s z = valAt x s z' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit <;> assumption)
end

