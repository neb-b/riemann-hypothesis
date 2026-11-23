module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0009
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PPointIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSumMeasurable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsSumMeasurable.proof : PtsSumMeasurable.Statement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  classical
  have hfin := fibreFinite K ι P e Ψ hP hΨ
  obtain ⟨B, γ, hBo, hlift, hcov⟩ := PtsSumMeasurable.exists_lift_family (P := P) (Ψ := Ψ) hfin
  have hind := sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs
  have hsheet : ∀ m, ∀ y ∈ B m, IsSheet P Ψ y (segre (γ m y)) (γ m) := fun m y hy =>
    ⟨rfl, Filter.eventually_of_mem ((hBo m).mem_nhds hy) fun y' hy' => hlift m y' hy'⟩
  have hγc : ∀ m, ContinuousOn (γ m) (B m) := fun m y hy =>
    (hlift m y hy).1.continuousAt.continuousWithinAt
  have hO : ∀ m, Set.MapsTo (γ m) (B m) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun m y hy =>
    (hlift m y hy).2.1.1
  have hseg : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) :=
    continuous_pi fun i => continuous_finsetProd _ fun k _ => continuous_apply _

  set σ : ℕ → (Fin e → ℂ) → ((k : K) → ι k) → ℂ := fun m =>
    (B m).piecewise (fun y => segre (γ m y)) 0 with hσdef
  have hσB : ∀ m, ∀ y ∈ B m, σ m y = segre (γ m y) := fun m y hy =>
    Set.piecewise_eq_of_mem _ _ _ hy
  have hσm : ∀ m, Measurable (σ m) := fun m =>
    (hseg.comp_continuousOn (hγc m)).measurable_piecewise continuousOn_const (hBo m).measurableSet

  set a : ℕ → (Fin e → ℂ) → ℝ := fun m => (B m).piecewise
    (fun y => ‖eval (γ m y) (map (Int.castRingHom ℂ) s)‖) 0 with hadef
  set b : ℕ → (Fin e → ℂ) → ℝ := fun m => (B m).piecewise (fun y => A.h (γ m y)) 1 with hbdef
  have ham : ∀ m, Measurable (a m) := fun m =>
    ((continuous_norm.comp (MvPolynomial.continuous_eval _)).comp_continuousOn
      (hγc m)).measurable_piecewise continuousOn_const (hBo m).measurableSet
  have hbm : ∀ m, Measurable (b m) := fun m =>
    ((ContDiffOn.continuousOn hA).comp (hγc m) (hO m)).measurable_piecewise continuousOn_const
      (hBo m).measurableSet
  set dens : ℕ → (Fin e → ℂ) → ℝ := fun m y =>
    Real.log (a m y / b m y) * maDensity (fun j y' => pot L j (γ m y')) y with hddef
  have hdm : ∀ m, Measurable (dens m) := fun m =>
    (Real.measurable_log.comp ((ham m).div (hbm m))).mul (PtsSumMeasurable.measurable_maDensity _)
  have hdens : ∀ m, ∀ y ∈ B m,
      dens m y = logNorm A s (γ m y) * maDensity (fun j y' => pot L j (γ m y')) y := by
    intro m y hy
    simp only [hddef, hadef, hbdef, Set.piecewise_eq_of_mem _ _ _ hy, logNorm]

  set S : ℕ → Set (Fin e → ℂ) := fun m =>
    {y | y ∈ B m ∧ ∀ m' < m, ¬ (y ∈ B m' ∧ σ m' y = σ m y)} with hSdef
  have hSm : ∀ m, MeasurableSet (S m) := by
    intro m
    have : S m = B m ∩ ⋂ m' ∈ Finset.range m, (B m' ∩ {y | σ m' y = σ m y})ᶜ := by
      ext y
      simp [hSdef]
      intro _
      constructor
      · intro h i hi
        by_cases hb : y ∈ B i
        · exact Or.inr (h i hi hb)
        · exact Or.inl hb
      · intro h i hi hb
        exact (h i hi).resolve_left (not_not.mpr hb)
    rw [this]
    exact (hBo m).measurableSet.inter (Finset.measurableSet_biInter _ fun m' _ =>
      ((hBo m').measurableSet.inter (measurableSet_eq_fun (hσm m') (hσm m))).compl)
  set f : ℕ → (Fin e → ℂ) → ℝ := fun m => (S m).indicator (dens m) with hfdef
  have hfm : ∀ m, Measurable (f m) := fun m => (hdm m).indicator (hSm m)
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N y => ∑ m ∈ Finset.range N, f m y)
    (fun N => (Finset.measurable_sum _ fun m _ => hfm m).aestronglyMeasurable) ?_
  filter_upwards [hind] with y hy

  have hterm : ∀ m, y ∈ S m → f m y = sheetDensity P Ψ (pot L) (logNorm A s) y (σ m y) := by
    intro m hm
    have hsh := hsheet m y hm.1
    rw [← hσB m y hm.1] at hsh
    have hex : ∃ γ', IsSheet P Ψ y (σ m y) γ' := ⟨_, hsh⟩
    rw [hfdef]
    simp only
    rw [Set.indicator_of_mem hm, hdens m y hm.1]
    unfold sheetDensity
    rw [dite_eq_left hex]
    exact (hy _ _ _ hex.choose_spec hsh).symm
  have hmemF : ∀ m, y ∈ S m → σ m y ∈ (hfin y).toFinset := by
    intro m hm
    rw [Set.Finite.mem_toFinset, hσB m y hm.1]
    exact ⟨γ m y, (hlift m y hm.1).2.1, rfl, (hlift m y hm.1).2.2⟩
  have hfy : ∀ m, (∑ w ∈ (hfin y).toFinset, if σ m y = w then f m y else 0) = f m y := by
    intro m
    rw [Finset.sum_ite_eq]
    by_cases hm : y ∈ S m
    · rw [if_pos (hmemF m hm)]
    · split_ifs
      · rfl
      · rw [hfdef]
        simp only
        rw [Set.indicator_of_notMem hm]
  have hev : ∀ w ∈ (hfin y).toFinset, ∀ᶠ N in atTop,
      sheetDensity P Ψ (pot L) (logNorm A s) y w =
        ∑ m ∈ Finset.range N, if σ m y = w then f m y else 0 := by
    intro w _
    by_cases hex : ∃ γ', IsSheet P Ψ y w γ'
    · obtain ⟨γ', hγ'⟩ := hex
      have hP' : ∃ m, y ∈ B m ∧ σ m y = w := by
        obtain ⟨m, hm, hmw⟩ := hcov y w γ' hγ'
        exact ⟨m, hm, (hσB m y hm).trans hmw⟩
      obtain ⟨hm1B, hm1w⟩ := Nat.find_spec hP'
      have hm1S : y ∈ S (Nat.find hP') :=
        ⟨hm1B, fun m' hm' h => Nat.find_min hP' hm' ⟨h.1, h.2.trans hm1w⟩⟩
      filter_upwards [eventually_gt_atTop (Nat.find hP')] with N hN
      rw [Finset.sum_eq_single_of_mem (Nat.find hP') (Finset.mem_range.2 hN), if_pos hm1w,
        hterm _ hm1S, hm1w]
      intro m _ hne
      split_ifs with hmw
      · by_cases hmS : y ∈ S m
        · exfalso
          have hle : Nat.find hP' ≤ m := Nat.find_min' hP' ⟨hmS.1, hmw⟩
          exact hmS.2 _ (lt_of_le_of_ne hle (Ne.symm hne)) ⟨hm1B, hm1w.trans hmw.symm⟩
        · rw [hfdef]
          simp only
          rw [Set.indicator_of_notMem hmS]
      · rfl
    · have h0 : sheetDensity P Ψ (pot L) (logNorm A s) y w = 0 := by
        unfold sheetDensity
        rw [dite_eq_right hex]
      refine Eventually.of_forall fun N => ?_
      rw [h0]
      refine (Finset.sum_eq_zero fun m _ => ?_).symm
      split_ifs with hmw
      · by_cases hmS : y ∈ S m
        · have hsh := hsheet m y hmS.1
          rw [← hσB m y hmS.1, hmw] at hsh
          exact absurd ⟨_, hsh⟩ hex
        · rw [hfdef]
          simp only
          rw [Set.indicator_of_notMem hmS]
      · rfl
  have hsum : ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, sheetDensity P Ψ (pot L) (logNorm A s) y w =
      ∑ w ∈ (hfin y).toFinset, sheetDensity P Ψ (pot L) (logNorm A s) y w :=
    finsum_mem_eq_finite_toFinset_sum _ (hfin y)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(eventually_all_finset _).2 hev] with N hN
  rw [hsum, Finset.sum_congr rfl hN, Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => hfy m

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartIntegral
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj IsSheet ptsIntegral
  ptsIntegralAt sheetDensity fibre maDensity mixedDisc cxHessian pot segre mcPts goodProjExists)

theorem maDensity_eq_zero_of_eventuallyEq_zero {D : ℕ} (φ : Fin (D + 1) → (Fin (D + 1) → ℂ) → ℝ)
    (y : Fin (D + 1) → ℂ) (h : φ 0 =ᶠ[𝓝 y] 0) : maDensity φ y = 0 := by
  have hH : fderiv ℝ (fderiv ℝ (φ 0)) y = 0 := by
    rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq]
    simp
  have hC : cxHessian (φ 0) y = 0 := by
    ext a b
    simp [cxHessian, hH]
  have hU : (fun k => cxHessian (φ k) y) =
      Function.update (fun k => cxHessian (φ k) y) 0 ((0 : ℂ) • (0 : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)) := by
    funext k
    by_cases hk : k = 0
    · subst hk
      simp [hC]
    · simp [Function.update_of_ne hk]
  have hM : mixedDisc (fun k => cxHessian (φ k) y) = 0 := by
    have hdef : mixedDisc (fun k => cxHessian (φ k) y) = ReciprocityTheory.AnForm.mdisc (fun k => cxHessian (φ k) y) :=
      rfl
    rw [hdef, hU, ReciprocityTheory.AnForm.A.mdisc_update_smul, zero_mul]
  simp [maDensity, hM]

theorem SegreChartIntegral.proof (hGood : SegreCoordGoodProj.Statement)
    (hIndep : PtsIntegralProjIndep.Statement) (hChart : PtsIntegralSegreChartProj.Statement) :
    SegreChartIntegral.Statement := by
  classical
  intro K _ _ ι _ P e m σ i L g δ G Φ hP hL hg hδ hsupp hgerm
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ), IsGoodProj P Ψ :=
    goodProjExists K ι P (e + 1) hP
  have hpts : ptsIntegral P (pot L) g = ptsIntegralAt P hex.choose (pot L) g := by
    unfold ptsIntegral
    rw [dite_eq_left hex]
  rw [hpts]
  by_cases hne : ∃ z ∈ mcPts P, segre z i ≠ 0
  · obtain ⟨Ψ, hΨ, hΨ0⟩ := hGood K ι P (e + 1) i hP hne
    rw [hIndep K ι P (e + 1) _ Ψ L g hP hex.choose_spec hΨ hL hg]
    exact hChart K ι P e m σ i L g Ψ G Φ hP hL hg hΨ hΨ0 hgerm
  · push Not at hne

    have hset : segreChartSet P σ i = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨z, hz, hzi, -⟩
      rw [hne z hz] at hzi
      exact zero_ne_one hzi
    have hcomp : segreChartComponents P σ i = ∅ := by
      ext J
      simp only [mem_segreChartComponents, Finset.notMem_empty, iff_false]
      intro hJ
      have htop : segreChartIdeal P σ i = ⊤ := by
        rw [segreChartIdeal, hset]
        exact MvPolynomial.vanishingIdeal_empty
      rw [htop] at hJ
      exact hJ.1.1.ne_top (top_le_iff.1 hJ.1.2)
    rw [hcomp, Finset.sum_empty]

    have hin : ∀ z ∈ mcPts P, ‖segre z i‖ < δ * ‖segre z‖ := by
      intro z hz
      rw [hne z hz, norm_zero]
      choose j hj using hz.1
      have hj' : segre z j ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hj k
      exact mul_pos hδ (norm_pos_iff.2 fun h0 => hj' (congrFun h0 j))
    have hterm : ∀ y w, sheetDensity P hex.choose (pot L) g y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · have hs : IsSheet P hex.choose y w hγ.choose := hγ.choose_spec
        rcases hsupp with hg0 | hp0
        · rw [hg0 _ (hin _ hs.2.self_of_nhds.2.1), zero_mul]
        · rw [maDensity_eq_zero_of_eventuallyEq_zero _ _ ?_, mul_zero]
          filter_upwards [hs.2] with y' hy'
          exact hp0 _ (hin _ hy'.2.1)
      · rfl
    unfold ptsIntegralAt
    simp [hterm]

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartIntegralPoints
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsMultiHomogIdeal ptsIntegral pot segre mcPts SameOrbit
  segre_smul mcPts_smul sameOrbit_of_segre)
open GroundTheory.Heights₂.Heights (varInt IsDegZeroSmooth segreChartSet segreChartComponents segreChartIdeal chartLift
  chartLift_segre_apply mem_segreChartComponents)

namespace SegreChartIntegralPoints

theorem aeval_eq_eval' {m : ℕ} (x : Fin m → ℂ) (p : MvPolynomial (Fin m) ℂ) : aeval x p = eval x p := rfl

theorem ker_eval_isMaximal {m : ℕ} (x : Fin m → ℂ) :
    (RingHom.ker (eval x : MvPolynomial (Fin m) ℂ →+* ℂ)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, eval_C _⟩

theorem minimalPrimes_vanishingIdeal {m : ℕ} {S : Set (Fin m → ℂ)} (hS : S.Finite) :
    (vanishingIdeal ℂ S : Ideal (MvPolynomial (Fin m) ℂ)).minimalPrimes =
      (fun x => RingHom.ker (eval x)) '' S := by
  classical
  have hle : ∀ x ∈ S, (vanishingIdeal ℂ S : Ideal (MvPolynomial (Fin m) ℂ)) ≤ RingHom.ker (eval x) :=
    fun x hx p hp => by rw [RingHom.mem_ker, ← aeval_eq_eval']; exact hp x hx
  have hinf : hS.toFinset.inf (fun x => RingHom.ker (eval x : MvPolynomial (Fin m) ℂ →+* ℂ)) ≤
      (vanishingIdeal ℂ S : Ideal (MvPolynomial (Fin m) ℂ)) := by
    intro p hp
    rw [mem_vanishingIdeal_iff]
    intro x hx
    have := Finset.inf_le (f := fun x => RingHom.ker (eval x : MvPolynomial (Fin m) ℂ →+* ℂ))
      (hS.mem_toFinset.2 hx) hp
    rwa [RingHom.mem_ker, ← aeval_eq_eval'] at this

  have hcont : ∀ q : Ideal (MvPolynomial (Fin m) ℂ), q.IsPrime → vanishingIdeal ℂ S ≤ q →
      ∃ x ∈ S, RingHom.ker (eval x) ≤ q := fun q hq hIq => by
    obtain ⟨x, hx, hxq⟩ := (hq.inf_le' (s := hS.toFinset)).1 (hinf.trans hIq)
    exact ⟨x, hS.mem_toFinset.1 hx, hxq⟩
  ext q
  constructor
  · intro hq
    obtain ⟨x, hx, hxq⟩ := hcont q hq.1.1 hq.1.2
    exact ⟨x, hx, le_antisymm hxq (hq.2 ⟨RingHom.ker_isPrime _, hle x hx⟩ hxq)⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨RingHom.ker_isPrime _, hle x hx⟩, fun q hq hqx => ?_⟩
    obtain ⟨y, hy, hyq⟩ := hcont q hq.1 hq.2
    have hxy := (ker_eval_isMaximal y).eq_of_le (ker_eval_isMaximal x).ne_top (hyq.trans hqx)
    show RingHom.ker (eval x) ≤ q
    rw [← hxy]
    exact hyq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem segre_ne_zero {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) : segre z ≠ 0 := by
  choose j hj using hz
  intro h
  have h0 : segre z j = 0 := by rw [h]; rfl
  exact Finset.prod_ne_zero_iff.2 (fun k _ => hj k) h0

theorem exists_normalised {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (k₀ : K) (i : (k : K) → ι k)
    {t : (Σ k, ι k) → ℂ} (ht : t ∈ mcPts P) (hi : segre t i ≠ 0) :
    ∃ t', t' ∈ mcPts P ∧ SameOrbit t' t ∧ segre t' = (segre t i)⁻¹ • segre t := by
  classical
  let c : K → ℂ := fun k => if k = k₀ then (segre t i)⁻¹ else 1
  have hc : ∀ k, c k ≠ 0 := fun k => by by_cases h : k = k₀ <;> simp [c, h, hi]
  have hprod : ∏ k, c k = (segre t i)⁻¹ := by
    rw [Finset.prod_eq_single k₀ (fun k _ hk => by simp [c, hk]) (by simp)]
    simp [c]
  exact ⟨_, mcPts_smul hP c hc ht, ⟨c, hc, rfl⟩, by rw [segre_smul, hprod]⟩

theorem proof : SegreChartIntegralPoints.Statement := by
  classical
  intro K _ _ ι _ P m σ i L g δ G Φ hP hg hδ hvan hG
  obtain ⟨k₀⟩ := hP.1
  obtain ⟨R, hRm, hRu, hRint⟩ := Inter.regularityPointsSum_holds.proof K ι P hP
  have horb : ∀ z z', SameOrbit z z' → g z = g z' := by
    rintro z z' ⟨c, hc, rfl⟩
    exact hg.2 c z' hc
  have hL : pot L = (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) := Subsingleton.elim _ _
  rw [hL, hRint g fun z z' _ h => horb z z' h]
  set S := R.filter (fun t => segre t i ≠ 0) with hS
  let ν : ((Σ k, ι k) → ℂ) → Fin m → ℂ := fun t a => (segre t i)⁻¹ * segre t (σ a)

  have hν : ∀ t ∈ S, ∃ t', t' ∈ mcPts P ∧ SameOrbit t' t ∧ segre t' i = 1 ∧
      ν t = fun a => segre t' (σ a) := by
    intro t ht
    obtain ⟨htR, hti⟩ := Finset.mem_filter.1 ht
    obtain ⟨t', ht'm, ht'o, ht's⟩ := exists_normalised hP.2.1.2.1 k₀ i (hRm t htR) hti
    refine ⟨t', ht'm, ht'o, ?_, funext fun a => ?_⟩
    · rw [ht's, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hti]
    · rw [ht's, Pi.smul_apply, smul_eq_mul]
  have hchart : segreChartSet P σ i = ν '' S := by
    ext x
    constructor
    · rintro ⟨z, hz, hzi, rfl⟩
      obtain ⟨t, ⟨htR, c, hc, rfl⟩, -⟩ := hRu z hz
      have hzs : segre (fun p => c p.1 * t p) = (∏ k, c k) • segre t := segre_smul c t
      have h1 : (∏ k, c k) * segre t i = 1 := by
        rw [← hzi, hzs, Pi.smul_apply, smul_eq_mul]
      have hti : segre t i ≠ 0 := right_ne_zero_of_mul_eq_one h1
      refine ⟨t, Finset.mem_filter.2 ⟨htR, hti⟩, funext fun a => ?_⟩
      rw [hzs, Pi.smul_apply, smul_eq_mul, eq_inv_of_mul_eq_one_left h1]
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨t', ht'm, -, ht'i, hνt⟩ := hν t ht
      exact ⟨t', ht'm, ht'i, hνt⟩
  have hinj : Set.InjOn ν S := by
    intro t₁ ht₁ t₂ ht₂ h
    obtain ⟨ht₁R, ht₁i⟩ := Finset.mem_filter.1 ht₁
    obtain ⟨ht₂R, ht₂i⟩ := Finset.mem_filter.1 ht₂
    have hseg : segre t₁ = (segre t₁ i * (segre t₂ i)⁻¹) • segre t₂ := by
      funext j
      have hj := congrFun h (σ.symm j)
      simp only [ν, Equiv.apply_symm_apply] at hj
      rw [Pi.smul_apply, smul_eq_mul, mul_assoc, ← hj, ← mul_assoc, mul_inv_cancel₀ ht₁i, one_mul]
    have h12 := sameOrbit_of_segre (hRm t₂ ht₂R).1 _ (mul_ne_zero ht₁i (inv_ne_zero ht₂i)) hseg
    exact (hRu t₁ (hRm t₁ ht₁R)).unique ⟨ht₁R, fun _ => 1, fun _ => one_ne_zero, by simp⟩ ⟨ht₂R, h12⟩
  have hfin : (segreChartSet P σ i).Finite := hchart ▸ S.finite_toSet.image ν
  have hfs : hfin.toFinset = S.image ν := Finset.coe_injective (by simp [hchart])
  have hcomp : segreChartComponents P σ i = hfin.toFinset.image (fun x => RingHom.ker (eval x)) := by
    ext J
    rw [mem_segreChartComponents, segreChartIdeal, minimalPrimes_vanishingIdeal hfin]
    simp
  have hkinj : ∀ x y : Fin m → ℂ, RingHom.ker (eval x : MvPolynomial (Fin m) ℂ →+* ℂ) = RingHom.ker (eval y) →
      x = y := fun x y h => by
    have := PointIntegral.zeroSet_ker_eval x
    rw [h, PointIntegral.zeroSet_ker_eval] at this
    exact (Set.singleton_eq_singleton_iff.1 this).symm
  rw [hcomp, Finset.sum_image fun x _ y _ h => hkinj x y h]
  rw [Finset.sum_congr rfl fun x _ => PointIntegral.proof m x G Φ]
  rw [hfs, Finset.sum_image hinj]

  rw [← Finset.sum_filter_of_ne (p := fun t => segre t i ≠ 0) fun t ht hgt hti => hgt (hvan t (by
    rw [hti, norm_zero]
    exact mul_pos hδ (norm_pos_iff.2 (segre_ne_zero (hRm t ht).1))))]
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨t', ht'm, ht'o, ht'i, hνt⟩ := hν t ht
  have hx : ν t ∈ segreChartSet P σ i := hchart ▸ Set.mem_image_of_mem ν ht
  rw [(hG _ hx).eq_of_nhds, Function.comp_apply, ← horb t' t ht'o, hνt]
  have hne : ∀ k, t' ⟨k, i k⟩ ≠ 0 := fun k h0 => by
    have h1 : segre t' i = 0 := Finset.prod_eq_zero (f := fun k => t' ⟨k, i k⟩) (Finset.mem_univ k) h0
    rw [ht'i] at h1
    exact one_ne_zero h1
  have hlift : chartLift σ i (fun a => segre t' (σ a)) = fun p => (t' ⟨p.1, i p.1⟩)⁻¹ * t' p := by
    funext ⟨k, j⟩
    rw [chartLift_segre_apply σ i t' ht'i k j, mul_comm]
  rw [hlift]
  exact (hg.2 (fun k => (t' ⟨k, i k⟩)⁻¹) t' fun k => inv_ne_zero (hne k)).symm

end SegreChartIntegralPoints

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsIntegrable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem abs_finsum_mem_le_finsum_mem_abs {α : Type*} (S : Set α) (f : α → ℝ) :
    |∑ᶠ w ∈ S, f w| ≤ ∑ᶠ w ∈ S, |f w| := by
  rw [finsum_mem_def, finsum_mem_def]
  have hind : S.indicator (fun w => |f w|) = fun w => |S.indicator f w| := by
    funext w
    by_cases hw : w ∈ S <;> simp [hw]
  rw [hind]
  have hsupp : Function.support (fun w => |S.indicator f w|) = Function.support (S.indicator f) := by
    ext w
    simp
  by_cases hfin : (Function.support (S.indicator f)).Finite
  · have hfin' : (Function.support (fun w => |S.indicator f w|)).Finite := hsupp ▸ hfin
    rw [finsum_eq_sum _ hfin, finsum_eq_sum _ hfin']
    have hs : hfin'.toFinset = hfin.toFinset := by
      ext w
      simp only [Set.Finite.mem_toFinset, hsupp]
    rw [hs]
    exact Finset.abs_sum_le_sum_abs _ _
  · have hinf' : ¬ (Function.support (fun w => |S.indicator f w|)).Finite := hsupp ▸ hfin
    rw [finsum_of_infinite_support hfin, finsum_of_infinite_support hinf', abs_zero]

theorem PtsIntegrable.of_found (hAbs : Inter.PtsAbsIntegrable.Statement)
    (hMeas : PtsSumMeasurable.Statement) : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  refine (hAbs K ι P e Ψ L A s hP hΨ hL hA hs).mono' (hMeas K ι P e Ψ L A s hP hΨ hL hA hs) ?_
  exact Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]
    exact abs_finsum_mem_le_finsum_mem_abs _ _

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisorComponents
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn divSupp IsHorizontal PBlk fsLine Xc)
open GroundTheory.Heights₂.Heights (segreChartComponents)

def ChartDivisorComponents.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → IsSectionOn P A s →
      (∀ J ∈ segreChartComponents P σ i, ∀ W' : Ideal (MvPolynomial (Fin m) ℂ),
        W' ∈ (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes ↔
          J ≤ W' ∧ ∃ W, (W ∈ divSupp P s ∧ IsHorizontal W) ∧ W' ∈ segreChartComponents W σ i) ∧
      ∀ W₁ W₂, W₁ ∈ divSupp P s ∧ IsHorizontal W₁ → W₂ ∈ divSupp P s ∧ IsHorizontal W₂ →
        ∀ W' ∈ segreChartComponents W₁ σ i, W' ∈ segreChartComponents W₂ σ i → W₁ = W₂

end GroundTheory.Heights₂.Heights.Targets
end
end

