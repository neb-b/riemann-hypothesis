module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.MetricLocal
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0104
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0060
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0028
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHolds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
public import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralIndependentOfMetric
section
set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

section FactorChange

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem snoc_update_comp_swap {D : ℕ} (W : Fin D → HermLine ι) (m : Fin D) (X B : HermLine ι) :
    (Fin.snoc (Function.update W m X) B : Fin (D + 1) → HermLine ι) ∘
        Equiv.swap m.castSucc (Fin.last D) =
      Fin.snoc (Function.update W m B) X := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Function.comp_apply, Equiv.swap_apply_right, Fin.snoc_castSucc, Function.update_self, Fin.snoc_last]
  · by_cases hi : i = m
    · subst hi
      rw [Function.comp_apply, Equiv.swap_apply_left, Fin.snoc_last, Fin.snoc_castSucc, Function.update_self]
    · have h1 : i.castSucc ≠ m.castSucc := fun h => hi (Fin.castSucc_injective _ h)
      have h2 : i.castSucc ≠ Fin.last D := (Fin.castSucc_lt_last i).ne
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.snoc_castSucc, Fin.snoc_castSucc,
        Function.update_of_ne hi, Function.update_of_ne hi]

theorem smooth_update {D : ℕ} {W : Fin D → HermLine ι} (hW : ∀ j, IsSmoothHerm (W j)) (m : Fin D)
    {X : HermLine ι} (hX : IsSmoothHerm X) (j : Fin D) : IsSmoothHerm (Function.update W m X j) := by
  by_cases hj : j = m
  · subst hj
    simpa using hX
  · simpa [Function.update_of_ne hj] using hW j

theorem smooth_snoc {D : ℕ} {W : Fin D → HermLine ι} (hW : ∀ j, IsSmoothHerm (W j)) {X : HermLine ι}
    (hX : IsSmoothHerm X) (j : Fin (D + 1)) :
    IsSmoothHerm ((Fin.snoc W X : Fin (D + 1) → HermLine ι) j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last]
    exact hX
  · rw [Fin.snoc_castSucc]
    exact hW i

theorem position_change (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) {D : ℕ} (hP : IsArithVar P (D + 1))
    (W : Fin D → HermLine ι) (hW : ∀ j, IsSmoothHerm (W j)) (m : Fin D) (A A' B : HermLine ι)
    (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A') (hB : IsSmoothHerm B) (hab : A'.a = A.a)
    (hloc : ∀ z ∈ mcPts P, ∃ c : ℝ, B.h =ᶠ[𝓝 z] fun _ => c) :
    I P (D + 1) (Fin.snoc (Function.update W m A) B) =
      I P (D + 1) (Fin.snoc (Function.update W m A') B) := by
  have hM := smooth_update hW m hB
  have hswap : ∀ X : HermLine ι, IsSmoothHerm X →
      I P (D + 1) (Fin.snoc (Function.update W m X) B) = I P (D + 1) (Fin.snoc (Function.update W m B) X) := by
    intro X hX
    rw [← snoc_update_comp_swap W m X B]
    exact (hI.1 P (D + 1) _ _ hP (smooth_snoc (smooth_update hW m hX) hB)).symm
  rw [hswap A hA, hswap A' hA',
    GlobalTheory.CompanionTheory.Ar.Tele.step GroundTheory.Heights₂.Heights.ForSecondHalf.MetricLocal.full I hI P D _ A A' hP hM hA hA' hab,
    _root_.GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst K ι P D (pot (Function.update W m B)) _ m ?_, sub_zero]
  intro z hz
  obtain ⟨c, hc⟩ := hloc z hz
  refine ⟨Real.log c, ?_⟩
  filter_upwards [hc] with x hx
  simp [pot, hx]

theorem word_change (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) {D : ℕ} (hP : IsArithVar P (D + 1))
    (L L' : Fin D → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (hL' : ∀ j, IsSmoothHerm (L' j))
    (ha : ∀ j, (L j).a = (L' j).a) (B : HermLine ι) (hB : IsSmoothHerm B)
    (hloc : ∀ z ∈ mcPts P, ∃ c : ℝ, B.h =ᶠ[𝓝 z] fun _ => c) :
    I P (D + 1) (Fin.snoc L B) = I P (D + 1) (Fin.snoc L' B) := by
  let Wd : ℕ → Fin D → HermLine ι := fun m j => if (j : ℕ) < m then L' j else L j
  have hWd : ∀ m j, IsSmoothHerm (Wd m j) := by
    intro m j
    by_cases h : (j : ℕ) < m
    · simpa [Wd, h] using hL' j
    · simpa [Wd, h] using hL j
  have key : ∀ m, m ≤ D → I P (D + 1) (Fin.snoc L B) = I P (D + 1) (Fin.snoc (Wd m) B) := by
    intro m
    induction m with
    | zero =>
      intro _
      have : Wd 0 = L := by
        funext j
        simp [Wd]
      rw [this]
    | succ m ih =>
      intro hm
      let i : Fin D := ⟨m, hm⟩
      have e0 : Function.update (Wd m) i (L i) = Wd m := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [Wd, i]
        · simp [Function.update_of_ne hj]
      have e1 : Function.update (Wd m) i (L' i) = Wd (m + 1) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [Wd, i]
        · have hne : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
          have hiff : (j : ℕ) < m + 1 ↔ (j : ℕ) < m := by omega
          simp [Function.update_of_ne hj, Wd, hiff]
      rw [ih (by omega), ← e1]
      conv_lhs => rw [← e0]
      exact position_change I hI P hP (Wd m) (hWd m) i (L i) (L' i) B (hL i) (hL' i) hB (ha i).symm hloc
  have hD : Wd D = L' := by
    funext j
    simp [Wd]
  rw [key D le_rfl, hD]

end FactorChange

theorem mass_eq_of_degrees : ArithIntersectionSystemStatement → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L L' : Fin D → HermLine ι) (sg : F →+* ℂ), IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) → (∀ j, (L j).a = (L' j).a) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) = ptsIntegral (mCoordIdeal y) (pot L') ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  intro hA hInt K _ ι _ Ω _ F _ _ _ y D L L' sg hP hL hL' ha hex
  classical
  obtain ⟨II, hII, -⟩ := hA
  let Λ : (F →+* ℂ) → ℝ := fun s => if s = sg then Real.exp 1 else 1
  have hΛ : ∀ s, 0 < Λ s := by
    intro s
    by_cases h : s = sg
    · simp [Λ, h, Real.exp_pos]
    · simp [Λ, h]
  obtain ⟨B, hB0, hBs, hBloc⟩ :=
    exists_smooth_weight_const_near_embeddings K ι Ω F y Λ hΛ hex
  have mass : ∀ M : Fin D → HermLine ι, (∀ j, IsSmoothHerm (M j)) →
      II K ι (mCoordIdeal y) (D + 1) (Fin.snoc M B) =
        ptsIntegral (mCoordIdeal y) (pot M) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
    intro M hM
    rw [intersection_locConst_trivial hInt K ι Ω F y D M B Λ II hII hP hM hB0 hBs hex hBloc,
      Finset.sum_eq_single sg]
    · simp [Λ]
    · intro s _ hs
      simp [Λ, hs]
    · intro h
      exact absurd (Finset.mem_univ sg) h
  rw [← mass L hL, ← mass L' hL']
  refine word_change (II K ι) (hII K ι) _ hP L L' hL hL' ha B hBs ?_
  intro z hz
  obtain ⟨s, hs, -⟩ := hex z hz
  exact ⟨Λ s, hBloc z hz s hs⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjChartSetEqSetChartSet
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

section Defs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def setChartSet (S : Set ((Σ k, ι k) → ℂ)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, Ψ (segre z) 0 = 1 ∧ x = fun a => segre z (σ a)}

def setChartIdeal (S : Set ((Σ k, ι k) → ℂ)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Ideal (MvPolynomial (Fin m) ℂ) :=
  vanishingIdeal ℂ (setChartSet S σ Ψ)

def setSegChartSet (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, segre z i = 1 ∧ x = fun a => segre z (σ a)}

def setSegChartIdeal (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Ideal (MvPolynomial (Fin m) ℂ) :=
  vanishingIdeal ℂ (setSegChartSet S σ i)

def setSegreCone (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, x = fun a => segre z (σ a)}

theorem isMultiHomogIdeal_toR {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal Q) :
    ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQ

theorem cone_scale {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) : (fun p => c p.1 * z p) ∈ conePts Q := by
  refine ⟨fun k => ?_, ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hQ c z hz.2⟩
  obtain ⟨i, hi⟩ := hz.1 k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem exists_segre_smul {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    [Nonempty K] {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) {c : ℂ} (hc : c ≠ 0) :
    ∃ z' ∈ conePts Q, segre z' = c • segre z := by
  classical
  obtain ⟨k0⟩ := ‹Nonempty K›
  refine ⟨_, cone_scale hQ (c := fun k => if k = k0 then c else 1) (fun k => ?_) hz, ?_⟩
  · split_ifs
    · exact hc
    · exact one_ne_zero
  · exact GoodChartZeroSet.segre_scaleBlock k0 c z

end Defs

section ZeroSet

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def liftPolyC [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (f : MRingOver ℂ ι) : MvPolynomial (Fin m) ℂ :=
  aeval (fun p : Σ k, ι k => (X (σ.symm (Function.update i p.1 p.2)) : MvPolynomial (Fin m) ℂ)) f

theorem eval_liftPolyC [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (x : Fin m → ℂ) (f : MRingOver ℂ ι) :
    eval x (liftPolyC σ i f) = eval (chartLift σ i x) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [liftPolyC]
  | add f g hf hg =>
    simp only [liftPolyC, map_add (f := _)] at hf hg ⊢
    rw [hf, hg]
  | mul_X f q hf =>
    simp only [liftPolyC, map_mul] at hf ⊢
    rw [hf]
    simp [chartLift]

theorem segChart_zeroSet {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) {m : ℕ}
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    zeroSet (setSegChartIdeal (conePts Q) σ i) = setSegChartSet (conePts Q) σ i := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ setSegChartSet (conePts Q) σ i, eval y q = 0) →
        eval x q = 0 :=
      fun q hq => hx q (by rw [setSegChartIdeal, mem_vanishingIdeal_iff]; exact hq)
    have ha : x (σ.symm i) = 1 := by
      have h := hv (X (σ.symm i) - 1) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        simp [hzi])
      rw [map_sub, eval_X, map_one] at h
      exact sub_eq_zero.1 h
    have hb : ∀ i' : (k : K) → ι k,
        x (σ.symm i') = ∏ k, x (σ.symm (Function.update i k (i' k))) := by
      intro i'
      have h := hv (X (σ.symm i') - ∏ k, X (σ.symm (Function.update i k (i' k)))) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        have hs : ∏ k, segre z (Function.update i k (i' k)) = segre z i' := by
          have h1 := congrFun (segre_chartLift σ i z hzi) i'
          simpa [ReciprocityTheory.ChartRestriction.G.Geo.segre, chartLift] using h1
        rw [map_sub, eval_X, map_prod]
        simp only [eval_X, Equiv.apply_symm_apply]
        rw [hs, sub_self])
      rw [map_sub, eval_X, map_prod] at h
      simp only [eval_X] at h
      exact sub_eq_zero.1 h
    have hc : ∀ f ∈ Q, eval (chartLift σ i x) f = 0 := by
      intro f hf
      rw [← eval_liftPolyC]
      refine hv _ ?_
      rintro _ ⟨z, hz, hzi, rfl⟩
      rw [eval_liftPolyC]
      have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
        have h1 : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
        rw [hzi] at h1
        exact one_ne_zero h1
      have hcl : chartLift σ i (fun a => segre z (σ a)) = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p := by
        funext ⟨k, j⟩
        rw [chartLift_segre_apply σ i z hzi, mul_comm]
      rw [hcl]
      exact (cone_scale hQ (c := fun k => (z ⟨k, i k⟩)⁻¹) (fun k => inv_ne_zero (hne k)) hz).2 f hf
    refine ⟨chartLift σ i x, ⟨chartLift_blockNonzero σ i ha, hc⟩, ?_, ?_⟩
    · show ∏ k, chartLift σ i x ⟨k, i k⟩ = 1
      simp [chartLift, ha]
    · funext a
      show x a = ∏ k, chartLift σ i x ⟨k, σ a k⟩
      simp only [chartLift]
      rw [← hb, Equiv.symm_apply_apply]
  · intro x hx q hq
    rw [setSegChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx

theorem chart_zeroSet {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) [Nonempty K]
    {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    zeroSet (setChartIdeal (conePts Q) σ Ψ) = setChartSet (conePts Q) σ Ψ := by
  classical
  apply Set.Subset.antisymm
  swap
  · intro x hx q hq
    rw [setChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx
  intro x hx
  have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ setChartSet (conePts Q) σ Ψ, eval y q = 0) → eval x q = 0 :=
    fun q hq => hx q (by rw [setChartIdeal, mem_vanishingIdeal_iff]; exact hq)
  have hseg : ∀ z : (Σ k, ι k) → ℂ, (fun i' => segre z (σ (σ.symm i'))) = segre z := fun z => by
    funext i'; rw [Equiv.apply_symm_apply]

  have hx1 : Ψ (fun i' => x (σ.symm i')) 0 = 1 := by
    have h := hv (GoodChartZeroSet.linForm σ Ψ - 1) (by
      rintro _ ⟨z, -, hz1, rfl⟩
      rw [map_sub, GoodChartZeroSet.eval_linForm, map_one, hseg, hz1, sub_self])
    rw [map_sub, GoodChartZeroSet.eval_linForm, map_one] at h
    exact sub_eq_zero.1 h
  obtain ⟨a, ha⟩ : ∃ a, x a ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have h0 : (fun i' => x (σ.symm i')) = 0 := funext fun i' => h _
    rw [h0, map_zero] at hx1
    exact zero_ne_one hx1

  have hzero : (x a)⁻¹ • x ∈ zeroSet (setSegChartIdeal (conePts Q) σ (σ a)) := by
    intro f hf
    rw [setSegChartIdeal, mem_vanishingIdeal_iff] at hf
    have hg := hv (X a * ∑ d ∈ Finset.range (f.totalDegree + 1),
        X a ^ (f.totalDegree - d) * homogeneousComponent d f) (by
      rintro _ ⟨z, hz, -, rfl⟩
      by_cases h0 : segre z (σ a) = 0
      · simp [h0]
      · rw [GoodChartZeroSet.eval_homogenize f le_rfl a _ h0]
        obtain ⟨z', hz', hz'e⟩ := exists_segre_smul hQ hz (inv_ne_zero h0)
        refine mul_eq_zero_of_right _ (hf _ ⟨z', hz', ?_, ?_⟩)
        · rw [hz'e, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ h0]
        · funext b
          rw [hz'e]
          rfl)
    rw [GoodChartZeroSet.eval_homogenize f le_rfl a x ha] at hg
    exact (mul_eq_zero.1 hg).resolve_left (pow_ne_zero _ ha)
  rw [segChart_zeroSet hQ σ (σ a)] at hzero
  obtain ⟨z', hz', -, hz'e⟩ := hzero
  obtain ⟨z, hz, hze⟩ := exists_segre_smul hQ hz' ha
  have hxz : x = fun b => segre z (σ b) := by
    funext b
    have hb := congrFun hz'e b
    simp only [Pi.smul_apply, smul_eq_mul] at hb
    rw [hze, Pi.smul_apply, smul_eq_mul, ← hb, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  refine ⟨z, hz, ?_, hxz⟩
  rw [← hseg z, ← hx1, hxz]

end ZeroSet

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFamilyEventuallySmoothPsh
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv.EvPsh

theorem tendsto_epsT_zero (C : ℝ) :
    Tendsto (fun t => epsT C t) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
  have hℓ : Tendsto (fun t : ℝ => Real.log (1 / t)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) atTop := by
    have h := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    refine h.congr (fun t => ?_)
    simp [one_div]
  have hq : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have h2 := (hq.comp hℓ).const_mul C
  rw [mul_zero] at h2
  refine h2.congr (fun t => ?_)
  simp only [Function.comp_apply, epsT]
  ring

theorem isPsh_of_isPosPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (h : IsPosPot A Θ) : IsPsh A Θ := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw
    simp [levi]
  · exact (h x j y hy w hw).le

theorem eventually_isPsh_add_pot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ)
    (C t₀ : ℝ) (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ) (hth : IsPotential A th)
    (hF : IsRegFamily A Θ L s th ph phT C t₀) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      A.Smooth (phT t) ∧ IsPsh A (th + LocPot.ofFun (phT t) + Θ) := by
  obtain ⟨ht₀, -, hF⟩ := hF
  have hε : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), epsT C t < 1 :=
    (tendsto_epsT_zero C).eventually (gt_mem_nhds one_pos)
  have hsmall : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioo 0 t₀ :=
    Ioo_mem_nhdsGT ht₀
  filter_upwards [hε, hsmall] with t hεt ht
  obtain ⟨h1, -, -, -, h5, -⟩ := hF t ht.1 ht.2.le
  refine ⟨h1, ?_⟩
  have h := GlobalTheory.CompanionTheory.Ar.Giv.isPsh_rsmul_mono A Θ th (phT t) hΘ (isPsh_of_isPosPot A Θ hΘp) hth h1 hεt.le h5
  have e1 : Θ.rsmul 1 = Θ := by
    cases Θ
    simp [LocPot.rsmul]
  rwa [e1] at h

end GlobalTheory.CompanionTheory.Ar.Giv.EvPsh
end

