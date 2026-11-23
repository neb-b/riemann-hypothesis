module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0062
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0060
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0047

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightPshAndBounds
section
set_option maxSynthPendingDepth 1

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
open ReciprocityTheory.AnForm.M.PLAux (analyticAt_compat)

section Charts

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem analyticAt_transition (P : PotentialCharts A) (j : Fin A.n) (k : Fin P.N) {y : Fin D → ℂ}
    (hy : y ∈ (A.chart j).target) (hk : (A.chart j).symm y ∈ (P.chart k).source) :
    AnalyticAt ℂ (P.chart k ∘ (A.chart j).symm) y := by
  have h := analyticAt_compat (P.compat k) j ((A.chart j).map_target hy) hk
  rwa [(A.chart j).right_inv hy] at h

theorem levi_th_add_chart (P : PotentialCharts A) (f : X → ℝ) (x : X) (j : Fin A.n) (k : Fin P.N)
    {y : Fin D → ℂ} (w : Fin D → ℂ) (hy : y ∈ (A.chart j).target)
    (hθ : (A.chart j).symm y ∈ P.th.U x) (hk : (A.chart j).symm y ∈ (P.chart k).source)
    (hcf : ContDiffAt ℝ 2 (P.chartFun f k) (P.chart k ((A.chart j).symm y))) :
    ContDiffAt ℝ 2 ((fun z => P.th.φ x z + f z) ∘ (A.chart j).symm) y ∧
      levi ((fun z => P.th.φ x z + f z) ∘ (A.chart j).symm) y w =
        levi (P.chartFun f k) (P.chart k ((A.chart j).symm y))
          (fderiv ℂ (P.chart k ∘ (A.chart j).symm) y w) := by
  have hg := analyticAt_transition P j k hy hk
  obtain ⟨W, hWo, hpW, G, hG, hEq⟩ := P.q_th k x _ ⟨hθ, hk⟩
  have hN : W ∩ P.th.U x ∩ (P.chart k).source ∈ 𝓝 ((A.chart j).symm y) :=
    ((hWo.inter (P.th.isOpen_U x)).inter (P.chart k).open_source).mem_nhds ⟨⟨hpW, hθ⟩, hk⟩
  have hev : (fun z => P.th.φ x z + f z) ∘ (A.chart j).symm =ᶠ[𝓝 y]
      fun y' => (P.chartFun f k ∘ (P.chart k ∘ (A.chart j).symm)) y' +
        (-1) * (G ((A.chart j).symm y')).re := by
    filter_upwards [((A.chart j).continuousAt_symm hy).preimage_mem_nhds hN] with y' hy'
    have h1 := hEq _ hy'
    simp only [Function.comp, PotentialCharts.chartFun, (P.chart k).left_inv hy'.2]
    linarith
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy, hpW⟩
  have hcf' : ContDiffAt ℝ 2 (P.chartFun f k) ((P.chart k ∘ (A.chart j).symm) y) := hcf
  have hcg : ContDiffAt ℝ 2 (P.chartFun f k ∘ (P.chart k ∘ (A.chart j).symm)) y :=
    hcf'.comp y ((hg.contDiffAt (n := 2)).restrict_scalars ℝ)
  have hre : ContDiffAt ℝ 2 (fun y' => (G ((A.chart j).symm y')).re) y := by
    have := (Complex.reCLM.contDiff (𝕜 := ℝ) (n := 2)).contDiffAt.comp y
      ((hGa.contDiffAt (n := 2)).restrict_scalars ℝ)
    simpa [Function.comp_def] using this
  have h0 : levi (fun y' => (G ((A.chart j).symm y')).re) y w = 0 := levi_re_analytic hGa w
  refine ⟨(hcg.add (contDiffAt_const.mul hre)).congr_of_eventuallyEq hev, ?_⟩
  rw [levi_congr hev w, levi_add_smul (-1) hcg hre w, h0, levi_comp w hg hcf']
  simp

theorem isPshOn_th_ph (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) :
    ReciprocityTheory.AnForm.P.IsPshOn A R.Yo (R.th + LocPot.ofFun R.ph) := by
  intro x j y hy w
  have hyt : y ∈ (A.chart j).target := hy.1
  have hθ : (A.chart j).symm y ∈ R.th.U x := hy.2.1.1
  have hY : (A.chart j).symm y ∈ R.Yo := hy.2.2
  obtain ⟨k, hk⟩ := R.cover ((A.chart j).symm y)
  have hks := R.toPotentialCharts.mid_subset_source k (R.inner_subset_mid k hk)
  have hξ : R.chart k ((A.chart j).symm y) ∈
      (R.chart k).target \ ReciprocityTheory.AnForm.A.coordDiv (R.S k) :=
    ⟨(R.chart k).map_source hks, (R.mem_Yo k _ hks).1 hY⟩
  have hUo : IsOpen ((R.chart k).target \ ReciprocityTheory.AnForm.A.coordDiv (R.S k)) :=
    (R.chart k).open_target.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _)
  have hC2 : ContDiffOn ℝ 2 (R.u k) ((R.chart k).target \ ReciprocityTheory.AnForm.A.coordDiv (R.S k)) :=
    fun ξ hξ => (RegChartData.contDiffAt_u R k hξ).contDiffWithinAt
  have hL := ((ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm _ _ _ hUo hC2).1 (R.u_psh k)).2
  have hcf : ContDiffAt ℝ 2 (R.chartFun R.ph k) (R.chart k ((A.chart j).symm y)) :=
    RegChartData.contDiffAt_u R k hξ
  have h := (levi_th_add_chart R.toPotentialCharts R.ph x j k w hyt hθ hks hcf).2
  change 0 ≤ levi ((fun z => R.th.φ x z + R.ph z) ∘ (A.chart j).symm) y w
  rw [h]
  exact hL _ hξ _

theorem exists_isPsh_of_chart_bound [CompactSpace X] (P : PotentialCharts A) (Θ : LocPot X)
    (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ) :
    ∃ c : Fin P.N → ℝ, (∀ k, 0 < c k) ∧ ∀ (f : X → ℝ) (a ε : ℝ), A.Smooth f → 0 ≤ ε →
      (∀ k : Fin P.N, ∀ x ∈ P.mid k, ∀ w : Fin D → ℂ,
        -a * ‖w‖ ^ 2 ≤ levi (P.chartFun f k) (P.chart k x) w) →
      (∀ k, a ≤ ε * c k) → IsPsh A (P.th + LocPot.ofFun f + Θ.rsmul ε) := by
  have hc : ∀ k : Fin P.N, ∃ c : ℝ, 0 < c ∧ ∀ p ∈ closure (P.mid k), ∀ x, p ∈ Θ.U x →
      ∀ v : Fin D → ℂ, c * ‖v‖ ^ 2 ≤ levi (Θ.φ x ∘ (P.chart k).symm) (P.chart k p) v := fun k =>
    exists_levi_lower hΘ hpos (P.compat k) isClosed_closure.isCompact (P.closure_mid k)
  choose c hc0 hc using hc
  refine ⟨c, hc0, fun f a ε hf hε hlev hac x j y hy w => ?_⟩
  have hyt : y ∈ (A.chart j).target := hy.1
  have hθ : (A.chart j).symm y ∈ P.th.U x := hy.2.1.1
  have hΘx : (A.chart j).symm y ∈ Θ.U x := hy.2.2
  have hpA : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hyt
  obtain ⟨k, hk⟩ := P.cover ((A.chart j).symm y)
  have hkm := P.inner_subset_mid k hk
  have hks := P.mid_subset_source k hkm
  have hcf : ContDiffAt ℝ 2 (P.chartFun f k) (P.chart k ((A.chart j).symm y)) := by
    have hq : ContDiffAt ℝ 2 (P.q k) (P.chart k ((A.chart j).symm y)) :=
      ((P.q_smooth k).contDiffAt ((P.chart k).open_target.mem_nhds
        ((P.chart k).map_source hks))).of_le (WithTop.coe_le_coe.2 le_top)
    exact hq.add (contDiffAt_comp_symm isOpen_univ hf (P.compat k) (Set.mem_univ _) hks)
  obtain ⟨hF, hFl⟩ := levi_th_add_chart P f x j k w hyt hθ hks hcf
  have hG : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y := by
    have := contDiffAt_comp_symm (Θ.isOpen_U x) (hΘ.1 x) (compat_chart A j) hΘx hpA
    rwa [(A.chart j).right_inv hyt] at this
  have hg := analyticAt_transition P j k hyt hks
  have hGl : levi (Θ.φ x ∘ (A.chart j).symm) y w =
      levi (Θ.φ x ∘ (P.chart k).symm) (P.chart k ((A.chart j).symm y))
        (fderiv ℂ (P.chart k ∘ (A.chart j).symm) y w) := by
    have hev := eventuallyEq_comp_chart (Θ.φ x) (P.chart k) (A.chart j) hyt hks
    have hcd : ContDiffAt ℝ 2 (Θ.φ x ∘ (P.chart k).symm) ((P.chart k ∘ (A.chart j).symm) y) :=
      contDiffAt_comp_symm (Θ.isOpen_U x) (hΘ.1 x) (P.compat k) hΘx hks
    rw [levi_congr hev w, levi_comp w hg hcd]
    rfl
  change 0 ≤ levi (fun y' => ((fun z => P.th.φ x z + f z) ∘ (A.chart j).symm) y' +
    ε * (Θ.φ x ∘ (A.chart j).symm) y') y w
  rw [levi_add_smul ε hF hG w, hFl, hGl]
  set v := fderiv ℂ (P.chart k ∘ (A.chart j).symm) y w
  have h1 := hlev k _ hkm v
  have h2 := hc k _ (subset_closure hkm) x hΘx v
  have h3 := mul_le_mul_of_nonneg_left h2 hε
  have h4 := mul_le_mul_of_nonneg_right (hac k) (sq_nonneg ‖v‖)
  nlinarith

end Charts

theorem tied_regularisation_weak : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B) (Θ : LocPot M.Xc), S.IsTied → IsPotential M.atlas Θ → IsPosPot M.atlas Θ → ReciprocityTheory.AnForm.P.IsPshOn M.atlas S.R.Yo (S.R.th + LocPot.ofFun S.R.ph) ∧ (∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) ∧ ∀ x ∈ S.R.Yo, S.R.ph x ≤ S.regWeight t x ∧ S.regWeight t x ≤ C) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), IsPsh M.atlas (S.R.th + LocPot.ofFun (S.regWeight t) + Θ.rsmul ε) := by
  intro K _ ι _ P n M Xo B S Θ hS hΘ hpos
  obtain ⟨C₀, t₀, ht₀, hb⟩ := GroundTheory.Heights₂.Heights.Regular.ChartMollifiedBounds.proof
    GroundTheory.Heights₂.Heights.Regular.TruncPsh.proof M.Xc n M.atlas S.R S.ρ
  refine ⟨isPshOn_th_ph S.R, ⟨C₀ + 1, ?_⟩, fun ε hε => ?_⟩
  · filter_upwards [S.eventually_chartLevi hS, self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht₀),
      hS.K_tendsto.eventually_ge_atTop 0,
      hS.e1_tendsto_zero.eventually (eventually_le_nhds one_pos)] with t hsm ht htt hK he
    have ht0 : (0 : ℝ) < t := ht
    have hε0 : 0 ≤ S.e1 t := ht0.le.trans (S.e1_ge t ht0)
    refine ⟨hsm.1, fun x hx => ⟨?_, ?_⟩⟩
    · obtain ⟨k, hk⟩ := S.R.cover x
      have hkm := S.R.inner_subset_mid k hk
      have h1 := ((hb t ht0 htt).2 (S.K t) hK k x hkm).2.2 hx
      have h2 := GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation.le_glue S.R.toPotentialCharts
        (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) hε0 hkm
      have h3 : S.regWeight t x = S.R.glue
          (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) (S.e1 t) x := rfl
      have hη := S.cutoff.eq_zero k x hk
      simp only [hη, mul_zero, add_zero] at h2
      rw [h3]
      linarith
    · have hg := GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation.glue_le S.R.toPotentialCharts
        (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) hε0 (c := C₀) (x := x)
        fun j hj => by
          have h1 := ((hb t ht0 htt).2 (S.K t) hK j x hj).2.1
          have h2 := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 4 * S.e1 t)
            (S.cutoff.bounds j x hj).2
          show S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x ≤ C₀
          linarith
      have h3 : S.regWeight t x = S.R.glue
          (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) (S.e1 t) x := rfl
      rw [h3]
      linarith
  · obtain ⟨c, hc0, hc⟩ := exists_isPsh_of_chart_bound S.R.toPotentialCharts Θ hΘ hpos
    have hlim : Tendsto (fun t => 4 * S.Cη * S.e1 t) (𝓝[>] 0) (𝓝 0) := by
      simpa using hS.e1_tendsto_zero.const_mul (4 * S.Cη)
    have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k, 4 * S.Cη * S.e1 t ≤ ε * c k :=
      Filter.eventually_all.2 fun k =>
        hlim.eventually (eventually_le_nhds (mul_pos hε (hc0 k)))
    filter_upwards [S.eventually_chartLevi hS, hall] with t ht hle
    exact hc (S.regWeight t) (4 * S.Cη * S.e1 t) ε ht.1 hε.le ht.2 hle

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSeventh
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem fibre_base_member : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ p, p ≠ (τ, a) → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = alphaOf BM l H bp p (Fin.tail z') + (Hh z').re := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hst hca hcb X q Un Gn ΦYn ΦWn l H bp hU hD p hp z hz
  obtain ⟨Hh, hHh, hev⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_member_potential K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hst hca hcb X q Un Gn
    ΦYn ΦWn l H bp hU hD p z hz
  refine ⟨Hh, hHh, ?_⟩
  filter_upwards [hev] with z' h
  rw [h]
  congr 1
  unfold alphaOf potAt
  congr 1
  by_cases hτ : p.1 = τ
  · have hpa : p.2 ≠ a := fun e => hp (Prod.ext hτ e)
    have hs := (_root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear.shear_main N j a b ca cb (z' 0) M.j_le hb hst hca hcb).2.2.2
      (BM.G l p.1 (bp (Fin.tail z'))) (H τ (Fin.tail z')) p.2 hpa
    simp only [flagAt, if_pos hτ]
    rw [hs, hτ]
  · simp only [flagAt, if_neg hτ]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSixth
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_fin_tail {d : ℕ} (z : Fin (d + 1) → ℂ) :
    AnalyticAt ℂ (Fin.tail : (Fin (d + 1) → ℂ) → Fin d → ℂ) z := by
  have : (Fin.tail : (Fin (d + 1) → ℂ) → Fin d → ℂ) =
      ⇑(ContinuousLinearMap.pi fun i : Fin d =>
        (ContinuousLinearMap.proj i.succ : (Fin (d + 1) → ℂ) →L[ℂ] ℂ)) := by
    funext u i
    rfl
  rw [this]
  exact ContinuousLinearMap.analyticAt _ z

theorem analyticAt_minorIJ {e N : ℕ} (A : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (z : Fin e → ℂ)
    (hA : ∀ r s, AnalyticAt ℂ (fun u => A u r s) z) (I J : Finset (Fin N)) :
    AnalyticAt ℂ (fun u => minorIJ (A u) I J) z := by
  unfold minorIJ
  by_cases h : I.card = J.card
  · simp only [h, dite_true, Matrix.det_apply, Matrix.submatrix_apply]
    refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
    simp only [Units.smul_def, zsmul_eq_mul]
    exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => hA _ _)
  · simp only [h, dite_false]
    exact analyticAt_const

theorem analyticAt_facOf {e N : ℕ} (j : ℕ) (a i : Fin N) (A : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (z : Fin e → ℂ)
    (hA : ∀ r s, AnalyticAt ℂ (fun u => A u r s) z) :
    AnalyticAt ℂ (fun u => facOf N j a (A u) i) z := by
  unfold facOf
  by_cases h₁ : (i : ℕ) + 1 = j
  · by_cases h₂ : (a : ℕ) < j
    · simp only [h₁, h₂, if_true]
      exact analyticAt_minorIJ A z hA _ _
    · simp only [h₁, h₂, if_true, if_false]
      exact analyticAt_const
  · simp only [h₁, if_false]
    exact analyticAt_minorIJ A z hA _ _

theorem fibre_xi_potential : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = xiPot (Gn (Fin.tail z')) (z' 0) + (Hh z').re := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hab hca hcb X q Un Gn ΦYn ΦWn l H bp hUn hD z hz
  have hD' := hD
  obtain ⟨hH, hbc, hbk, hpt, hG, -, -⟩ := hD'
  choose Hp hPa hPe using fun p => _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_member_potential K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hab hca hcb X q Un Gn ΦYn
    ΦWn l H bp hUn hD p z hz
  have htail : ∀ᶠ z' : Fin (d + 1) → ℂ in 𝓝 z, Fin.tail z' ∈ Un :=
    (analyticAt_fin_tail z).continuousAt.preimage_mem_nhds (hUn.mem_nhds hz)
  have hHa : ∀ τ' r s, AnalyticAt ℂ (fun u => H τ' (Fin.tail u) r s) z := fun τ' r s =>
    AnalyticAt.comp (g := fun w => H τ' w r s) (hH τ' r s _ hz) (analyticAt_fin_tail z)
  have hfac : ∀ i : Fin N, ∃ A : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ A z ∧ ∀ᶠ z' in 𝓝 z,
      (if IsProperStep N j i then 0 else Real.log ‖facOf N j a (H τ (Fin.tail z')) i‖) = (A z').re := by
    intro i
    by_cases hp : IsProperStep N j i
    · exact ⟨fun _ => 0, analyticAt_const, Eventually.of_forall fun z' => by simp [hp]⟩
    · obtain ⟨A, hA, hAe⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_eventually_eq_re_analyticAt (d + 1) (fun u => facOf N j a (H τ (Fin.tail u)) i) z
        (analyticAt_facOf j a i (fun u => H τ (Fin.tail u)) z (hHa τ))
        (GlobalTheory.T.step_factor_ne_zero N j a i _ ((hpt _ hz).2 τ).1 ((hpt _ hz).2 τ).2)
      exact ⟨A, hA, hAe.mono fun z' h => by simpa [hp] using h⟩
  have hups : ∀ i : Fin N, ∃ A : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ A z ∧ ∀ᶠ z' in 𝓝 z,
      upsLogAt BM l (τ, i) (bp (Fin.tail z')) = (A z').re := by
    intro i
    by_cases hp : M.blk (τ, i) = none
    · have hO : bp (Fin.tail z) ∈ BM.O l := (hpt _ hz).1.1
      have hreg := ((BM.good l _ hO).2.2 (τ, i) hp).2.1
      have hv := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.analyticAt_valAt_lift_family (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x ((BM.F l).υ (τ, i)) d n BM.Rb Un bp (Fin.tail z)
        hUn hz hbc hbk hreg
      have hf : AnalyticAt ℂ (fun u => upsVal BM l (τ, i) (bp (Fin.tail u))) z :=
        AnalyticAt.comp (g := fun w => valAt M.x ((BM.F l).υ (τ, i)) (BM.Rb.lift (bp w) (bp w))) hv
          (analyticAt_fin_tail z)
      obtain ⟨A, hA, hAe⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_eventually_eq_re_analyticAt (d + 1) _ z hf
        (_root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.UpsNe.upsVal_ne_zero K ι Φ y Ψ N j M n d BM l (τ, i) _ hO hp)
      exact ⟨A, hA, hAe.mono fun z' h => by simpa [upsLogAt, hp] using h⟩
    · exact ⟨fun _ => 0, analyticAt_const, Eventually.of_forall fun z' => by simp [upsLogAt, hp]⟩
  choose Lf hLa hLe using hfac
  choose Uf hUa hUe using hups
  refine ⟨fun u => ∑ p, ((xiCoef τ a p : ℝ) : ℂ) * Hp p u -
    ∑ i, ((xiCoef τ a (τ, i) : ℝ) : ℂ) * (Lf i u + Uf i u), ?_, ?_⟩
  · refine AnalyticAt.sub (Finset.analyticAt_fun_sum _ fun p _ => analyticAt_const.mul (hPa p))
      (Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul ((hLa i).add (hUa i)))
  · filter_upwards [htail, eventually_all.2 hPe, eventually_all.2 hLe, eventually_all.2 hUe] with z' hw h1 h2 h3
    have hs : ∑ p, (xiCoef τ a p : ℝ) * potAt BM l p (bp (Fin.tail z')) (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) =
        xiPot (Gn (Fin.tail z')) (z' 0) - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) *
          ((if IsProperStep N j i then 0 else Real.log ‖facOf N j a (H τ (Fin.tail z')) i‖) +
            upsLogAt BM l (τ, i) (bp (Fin.tail z'))) :=
      _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.xi_sum_potentials Ψ N j τ a b ca cb (fun τ' => BM.G l τ' (bp (Fin.tail z'))) (fun τ' => H τ' (Fin.tail z'))
        (fun p => upsLogAt BM l p (bp (Fin.tail z'))) (z' 0) (Gn (Fin.tail z')) M.j_le hb hab hca hcb
        (BM.G_pos l τ _ (hpt _ hw).1).1 (BM.G_pos l τ _ (hpt _ hw).1).2 ((hpt _ hw).2 τ).1 ((hpt _ hw).2 τ).2
        (hG _ hw)
    have e1 : ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') =
        ∑ p, (xiCoef τ a p : ℝ) * potAt BM l p (bp (Fin.tail z')) (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) +
          ∑ p, (xiCoef τ a p : ℝ) * (Hp p z').re := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => by rw [h1 p, mul_add]
    have e3 : ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) *
          ((if IsProperStep N j i then 0 else Real.log ‖facOf N j a (H τ (Fin.tail z')) i‖) +
            upsLogAt BM l (τ, i) (bp (Fin.tail z'))) =
        ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((Lf i z').re + (Uf i z').re) :=
      Finset.sum_congr rfl fun i _ => by rw [h2 i, h3 i]
    rw [e1, hs, e3]
    simp only [Complex.sub_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

