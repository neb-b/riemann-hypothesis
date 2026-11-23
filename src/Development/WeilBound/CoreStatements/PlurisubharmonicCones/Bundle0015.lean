module

public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0089
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0008
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LeviShift
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.OneSlot
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.MolliLeOfLe
section
open MeasureTheory Metric Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open ReciprocityTheory.AnForm.A (Mollifier molli coordDiv)

noncomputable section

namespace LevelTowerAlt.Comparison₂

theorem molli_le_of_le {D : ℕ} (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
    (hU : IsOpen U) (hφ : ReciprocityTheory.AnForm.A.IsPsh U φ) {t c : ℝ} (ht : 0 < t) {z : Fin D → ℂ}
    (hz : closedBall z t ⊆ U) (hc : ∀ y ∈ closedBall z t, φ y ≤ c) : molli ρ t φ z ≤ c := by
  obtain ⟨-, hi⟩ := ReciprocityTheory.AnForm.A.phiC hU hφ (isCompact_closedBall z t) hz
  rw [ReciprocityTheory.AnForm.A.molli_eq_C ρ ht (subset_refl _)]
  calc _ ≤ ∫ y, ρ.scaled t y * c := by
        refine integral_mono (ReciprocityTheory.AnForm.A.integrable_kC ρ ht hi z)
          ((ReciprocityTheory.AnForm.A.integrable_scaled ρ ht).mul_const _) fun y => ?_
        by_cases hy : ρ.scaled t y = 0
        · simp [hy]
        refine mul_le_mul_of_nonneg_left ?_ (ReciprocityTheory.AnForm.A.scaled_nonneg ρ ht y)
        have hmem := ReciprocityTheory.AnForm.A.mem_ball_sub ρ ht hy z
        rw [indicator_of_mem hmem]
        exact hc _ hmem
    _ = c := by rw [integral_mul_const, ReciprocityTheory.AnForm.A.integral_scaled ρ ht, one_mul]

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem neBot_Yo (R : RegChartData A) (x : X) : (𝓝[R.Yo] x).NeBot := by
  obtain ⟨k, hk⟩ := R.cover x
  have hs := R.toPotentialCharts.mid_subset_source k (R.inner_subset_mid k hk)
  have hne := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := R.S k) (R.chart k).open_target ((R.chart k).map_source hs)
  have ht : Tendsto (R.chart k).symm (𝓝[(R.chart k).target \ coordDiv (R.S k)] (R.chart k x)) (𝓝[R.Yo] x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := ((R.chart k).continuousAt_symm ((R.chart k).map_source hs)).tendsto
      rw [(R.chart k).left_inv hs] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      rw [R.mem_Yo k _ ((R.chart k).map_target hy.1), (R.chart k).right_inv hy.1]
      exact hy.2
  exact ht.neBot

theorem phReg_le [CompactSpace X] [T2Space X] (R : RegChartData A) (ρ : Mollifier D) (Kt : ℝ → ℝ)
    (hK : Tendsto Kt (𝓝[>] 0) atTop) {V K' : Set X} {g : X → ℝ} (hV : IsOpen V) (hg : ContinuousOn g V)
    (hph : ∀ x ∈ V ∩ R.Yo, g x = R.ph x) (hK'V : K' ⊆ V) (hK' : IsCompact K') (j : Fin R.N) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∈ K', x ∈ R.mid j → R.phReg ρ (Kt t) t j x ≤ g x + ε := by
  obtain ⟨δ, B, hδ, hT⟩ := TruncPsh.proof X D A R
  obtain ⟨U, hU, -, hUb, hUp⟩ := hT j
  set L := R.chart j '' (K' ∩ closure (R.mid j)) with hL
  have hsub : K' ∩ closure (R.mid j) ⊆ (R.chart j).source := fun x hx => R.closure_mid j hx.2
  have hLc : IsCompact L := (hK'.inter_right isClosed_closure).image_of_continuousOn ((R.chart j).continuousOn.mono hsub)
  set O := (R.chart j).target ∩ (R.chart j).symm ⁻¹' V with hO
  have hOo : IsOpen O := (R.chart j).isOpen_inter_preimage_symm hV
  have hLO : L ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(R.chart j).map_source (hsub hx), ?_⟩
    show (R.chart j).symm _ ∈ V
    rw [(R.chart j).left_inv (hsub hx)]
    exact hK'V hx.1
  let F : (Fin D → ℂ) → ℝ := fun y => R.q j y + g ((R.chart j).symm y)
  have hF : ContinuousOn F O := ((R.q_smooth j).continuousOn.mono inter_subset_left).add
    (hg.comp ((R.chart j).continuousOn_symm.mono inter_subset_left) fun y hy => hy.2)
  obtain ⟨η, hη, hηO⟩ := hLc.exists_cthickening_subset_open hOo hLO
  obtain ⟨d, hd, hdF⟩ := Metric.uniformContinuousOn_iff.1
    ((hLc.cthickening (r := η)).uniformContinuousOn_of_continuous (hF.mono hηO)) ε hε
  obtain ⟨M, hM⟩ := hLc.exists_bound_of_continuousOn (hF.mono hLO)
  have hsm : ∀ {a : ℝ}, 0 < a → ∀ᶠ t in 𝓝[>] (0 : ℝ), t < a := fun ha =>
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ha)
  filter_upwards [self_mem_nhdsWithin, hsm hδ, hsm (half_pos hη), hsm (half_pos hd), hK.eventually_ge_atTop M]
    with t ht t1 t2 t3 t4 x hx hxm
  have ht0 : (0 : ℝ) < t := ht
  have hxL : R.chart j x ∈ L := ⟨x, ⟨hx, subset_closure hxm⟩, rfl⟩
  have hxs := hsub ⟨hx, subset_closure hxm⟩
  have hFx : F (R.chart j x) = R.q j (R.chart j x) + g x := by simp only [F, (R.chart j).left_inv hxs]
  have h1 : molli ρ t (R.trunc (Kt t) j) (R.chart j x) ≤ F (R.chart j x) + ε := by
    refine molli_le_of_le ρ hU (hUp _).1 ht0 ((closedBall_subset_closedBall t1.le).trans (hUb x hxm)) fun y hy => ?_
    have hyx : dist y (R.chart j x) ≤ t := hy
    have hyO : y ∈ O := hηO (mem_cthickening_of_dist_le y _ _ _ hxL (by linarith))
    refine TruncTransfer.limsupExt_max_le (R.chart j).open_target (R.S j) (R.u j) _ _ t hyO.1 ht0 fun y' hy' hy't hy'S => ?_
    have h2 : dist y' (R.chart j x) < 2 * t := by
      have := dist_triangle y' y (R.chart j x)
      have h3 : dist y' y < t := hy'
      linarith
    have hy'c : y' ∈ cthickening η L := mem_cthickening_of_dist_le y' _ _ _ hxL (by linarith)
    have h4 := hdF y' hy'c _ (self_subset_cthickening L hxL) (by linarith)
    have h5 : R.u j y' = F y' := by
      show R.q j y' + R.ph _ = R.q j y' + g _
      rw [hph _ ⟨(hηO hy'c).2, by
        rw [R.mem_Yo j _ ((R.chart j).map_target hy't), (R.chart j).right_inv hy't]
        exact hy'S⟩]
    rw [Real.dist_eq] at h4
    have h6 := hM _ hxL
    rw [Real.norm_eq_abs] at h6
    refine max_le ?_ ?_
    · rw [h5]
      linarith [(abs_lt.1 h4).2]
    · linarith [(abs_le.1 h6).1]
  show molli ρ t (R.trunc (Kt t) j) (R.chart j x) - R.q j (R.chart j x) ≤ _
  linarith

theorem regUnif : RegUnif := by
  intro K _ J _ P n M Xo B S V g hS hV hg hph
  obtain ⟨C₀, t₀, ht₀, hb⟩ := ChartMollifiedBounds.proof TruncPsh.proof M.Xc n M.atlas S.R S.ρ
  have h3 : ∀ t x, S.regWeight t x = S.R.glue
      (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) (S.e1 t) x := fun _ _ => rfl
  have hup : ∀ t, 0 < t → ∀ x c, (∀ j, x ∈ S.R.mid j → S.R.phReg S.ρ (S.K t) t j x ≤ c) →
      S.regWeight t x ≤ c + S.e1 t := by
    intro t ht0 x c h
    have hε0 : 0 ≤ S.e1 t := ht0.le.trans (S.e1_ge t ht0)
    rw [h3]
    refine LogLogRegularisation.glue_le S.R.toPotentialCharts _ hε0 fun j hj => ?_
    have h2 := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 4 * S.e1 t) (S.cutoff.bounds j x hj).2
    have := h j hj
    show S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x ≤ c
    linarith
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ x, S.regWeight t x ≤ C₀ + 1) ∧ ∀ x ∈ V, g x ≤ S.regWeight t x := by
    filter_upwards [S.eventually_chartLevi hS, self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht₀), hS.K_tendsto.eventually_ge_atTop 0,
      hS.e1_tendsto_zero.eventually (eventually_le_nhds one_pos)] with t hsm ht htt hK he
    have ht0 : (0 : ℝ) < t := ht
    have hε0 : 0 ≤ S.e1 t := ht0.le.trans (S.e1_ge t ht0)
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · have := hup t ht0 x C₀ fun j hj => ((hb t ht0 htt).2 (S.K t) hK j x hj).2.1
      linarith
    · have hlow : ∀ x ∈ S.R.Yo, S.R.ph x ≤ S.regWeight t x := by
        intro x hx
        obtain ⟨k, hk⟩ := S.R.cover x
        have hkm := S.R.inner_subset_mid k hk
        have a1 := ((hb t ht0 htt).2 (S.K t) hK k x hkm).2.2 hx
        have a2 := LogLogRegularisation.le_glue S.R.toPotentialCharts
          (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) hε0 hkm
        simp only [S.cutoff.eq_zero k x hk, mul_zero, add_zero] at a2
        rw [h3]
        linarith
      have := neBot_Yo S.R x
      have c1 : Tendsto g (𝓝[S.R.Yo] x) (𝓝 (g x)) := (hg.continuousAt (hV.mem_nhds hx)).tendsto.mono_left nhdsWithin_le_nhds
      have c2 : Tendsto (S.regWeight t) (𝓝[S.R.Yo] x) (𝓝 (S.regWeight t x)) :=
        ((GlobalTheory.CompanionTheory.Ar.Cmp.OneModel.continuous_of_smooth M.atlas hsm.1).tendsto x).mono_left nhdsWithin_le_nhds
      refine le_of_tendsto_of_tendsto c1 c2 ?_
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hx)] with y hy hyV
      rw [hph y ⟨hyV, hy⟩]
      exact hlow y hy
  refine ⟨⟨C₀ + 1, h1⟩, fun K' hK'V hK' => Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_⟩
  filter_upwards [h1, self_mem_nhdsWithin, hS.e1_tendsto_zero.eventually (eventually_lt_nhds (half_pos hε)),
    eventually_all.2 fun j => phReg_le S.R S.ρ S.K hS.K_tendsto hV hg hph hK'V hK' j (half_pos hε)] with t a1 ht a2 a3 x hx
  have a4 := hup t ht x (g x + ε / 2) fun j hj => a3 j x hx hj
  have a5 := a1.2 x (hK'V hx)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end LevelTowerAlt.Comparison₂
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.SmoothLogSub
section
open Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

noncomputable section

namespace LevelTowerAlt.Comparison₂

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P B : Ideal (MRing J)} {e : ℕ}

theorem log_sub_lift (R : AnLogRes P B e) {A A' : HermLine J} (h : A.a = A'.a) (x : R.X) {y : R.X} (hy : y ∈ R.U x) :
    Real.log (A.h (R.lift x y)) = Real.log (A'.h (R.lift x y)) +
      (Real.log (A.h (R.lift y y)) - Real.log (A'.h (R.lift y y))) := by
  obtain ⟨c, hc, e⟩ := R.compat y x y ⟨R.mem_U y, hy⟩
  have hz := (R.mem x y hy).1
  have hp : (∏ k, ‖c k‖ ^ A'.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [e, A.smul c _ hc, A'.smul c _ hc, h, Real.log_mul hp (A.pos _ hz).ne', Real.log_mul hp (A'.pos _ hz).ne']
  ring

theorem smooth_log_sub (R : AnLogRes P B e) {A A' : HermLine J} (h : A.a = A'.a) (hA : IsSmoothHerm A)
    (hA' : IsSmoothHerm A') : R.A.Smooth fun y => Real.log (A.h (R.lift y y)) - Real.log (A'.h (R.lift y y)) := by
  intro j y hy
  have hn := ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U ((R.A.chart j).symm y))).mem_nhds
    ⟨hy.1, R.mem_U _⟩
  have h1 := (((potOf_isPotential R A hA).1 ((R.A.chart j).symm y) j).sub
    ((potOf_isPotential R A' hA').1 ((R.A.chart j).symm y) j)).contDiffAt hn
  refine (h1.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hn] with z hz
  have := log_sub_lift R h ((R.A.chart j).symm y) hz.2
  show _ - _ = Real.log (A.h (R.lift _ _)) - Real.log (A'.h (R.lift _ _))
  linarith

theorem position_zero {I : Ideal (MRing J) → (n : ℕ) → (Fin n → HermLine J) → ℝ} (hI : IsIntersectionFamily I)
    (R : AnLogRes P B e) {Θ L : LocPot R.X} {s : R.X → R.X → ℂ} {nb : ℕ} {mb : Fin nb → ℕ} {Wb : Fin nb → Set R.X}
    (hP : IsArithVar P (e + 1)) (hΘ : IsPotential R.A Θ) (hΘp : IsPosPot R.A Θ) (hL : IsPotential R.A L)
    (hs : IsSection R.A L s) (hsnc : IsSNC R.A L s mb Wb) (hle : ∀ x, logNormSec L s x ≤ 0)
    (l : Fin e → ℝ → HermLine J) (hl : ∀ j, Tame R Θ L s (l j)) {A₁ A₂ : ℝ → HermLine J} {f g : MRing J}
    {w : ℝ → ((Σ k, J k) → ℂ) → ℝ} {C : ℝ} (hsm : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (A₁ t) ∧ IsSmoothHerm (A₂ t))
    (hw : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsLineIso P (A₁ t).a (A₂ t).a f g ∧ IsDefectOn P (mcPts P) f g (A₁ t) (A₂ t) (w t) ∧
      ∀ x ∉ bdry s, |w t (R.lift x x)| ≤ C * Real.log (rW L s x))
    (hw0 : ∀ K' ⊆ (bdry s)ᶜ, IsCompact K' →
      TendstoUniformlyOn (fun t x => w t (R.lift x x)) (fun _ => 0) (𝓝[>] 0) K') :
    Tendsto (fun t => I P (e + 1) (Fin.snoc (fun j => l j t) (A₂ t)) - I P (e + 1) (Fin.snoc (fun j => l j t) (A₁ t)))
      (𝓝[>] 0) (𝓝 0) := by
  choose ref c href hev using hl
  have h := weak_zero R.A Θ L s mb Wb hΘ hΘp hL hs hsnc hle (fun j => potOf R (ref j))
    (fun j => potOf_isPotential R _ (href j)) (fun t j => potOf R (l j t))
    (fun t j y => Real.log ((l j t).h (R.lift y y)) - Real.log ((ref j).h (R.lift y y))) (fun t x => w t (R.lift x x)) c C
    (fun j => (hev j).mono fun t ht => ⟨smooth_log_sub R ht.2.1 ht.1 (href j), potOf_isPotential R _ ht.1, fun _ => rfl,
      fun x y hy => log_sub_lift R ht.2.1 x hy, ht.2.2.1, ht.2.2.2⟩) ?_ hw0
  · refine h.congr' ?_
    filter_upwards [hsm, hw, eventually_all.2 hev] with t h1 h2 h3
    have := one_coord₂ _root_.GlobalTheory.CompanionTheory.Ar.Link.resBridgeStatement_holds Link.goodProjExistsStatement_holds hI R (fun j => l j t) (A₁ t) (A₂ t) f g (w t) hP
      (fun j => (h3 j).1) h1.1 h1.2 h2.1 h2.2.1
    linarith
  · filter_upwards [hsm, hw] with t h1 h2
    refine ⟨?_, h2.2.2⟩
    obtain ⟨w', a1, -, a2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.defect_exists_smooth K J P B e R (A₁ t) (A₂ t) f g hP.2.1 h2.1 h1.1 h1.2
    refine (OneModel.continuous_of_smooth R.A a2).congr fun x => ?_
    have hz := R.mem x x (R.mem_U x)
    obtain ⟨u, v, huv, hu, -⟩ := OneModel.exists_pair_ne h2.1.2 hz
    rw [a1 _ hz u v huv hu, h2.2.1 _ hz u v huv hu]

theorem comb_single {τ : Type} [Fintype τ] [DecidableEq τ] (l : τ → HermLine J) (a : τ) :
    Top.combLine l (Pi.single a 1) = l a := by
  refine OneSlot.hermLine_ext ?_ (funext fun z => ?_)
  · show ∑ j, (Pi.single a 1 : τ → ℤ) j • (l j).a = _
    simp [Pi.single_apply]
  · show ∏ j, (l j).h z ^ (Pi.single a 1 : τ → ℤ) j = _
    rw [Finset.prod_eq_single a]
    · simp
    · intro b _ hb
      simp [hb]
    · simp

theorem ii_comb_snoc {II : IntersectionSystem} (hII : IsFullIntersectionSystem II) (hP : IsArithVar P (e + 1)) {τ : Type}
    [Fintype τ] [DecidableEq τ] (l : τ → HermLine J) (hl : ∀ a, IsSmoothHerm (l a)) (ν : Fin e → τ → ℤ) (a : τ) :
    II K J P (e + 1) (Fin.snoc (fun k => Top.combLine l (ν k)) (l a)) =
      ∑ w : Fin e → τ, (∏ k, (ν k (w k) : ℝ)) * II K J P (e + 1) (Fin.snoc (fun k => l (w k)) (l a)) := by
  have h := _root_.GlobalTheory.CompanionTheory.Ar.Top.intersection_combLine_expansion II hII K J P (e + 1) τ l (Fin.snoc (α := fun _ => τ → ℤ) ν (Pi.single a 1)) hP hl
  have h1 : (fun k => Top.combLine l (Fin.snoc (α := fun _ => τ → ℤ) ν (Pi.single a 1) k)) =
      Fin.snoc (α := fun _ => HermLine J) (fun k => Top.combLine l (ν k)) (l a) := by
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp [comb_single]
    · simp
  rw [← h1, h, ← (Fin.snocEquiv fun _ => τ).sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun w _ => ?_
    congr 1
    · simp [Fin.prod_univ_castSucc, Fin.snocEquiv]
    · congr 1
      funext k
      refine Fin.lastCases ?_ (fun k => ?_) k <;> simp [Fin.snocEquiv]
  · intro b _ hb
    refine Finset.sum_eq_zero fun w _ => ?_
    simp [Fin.prod_univ_castSucc, Fin.snocEquiv, hb]
  · simp

theorem replace_gen {II : IntersectionSystem} (hII : IsFullIntersectionSystem II) {d : ℕ} (hd : d = e + 1)
    (R : AnLogRes P B e) {Θ L : LocPot R.X} {s : R.X → R.X → ℂ} {nb : ℕ} {mb : Fin nb → ℕ} {Wb : Fin nb → Set R.X}
    (hP : IsArithVar P (e + 1)) (hΘ : IsPotential R.A Θ) (hΘp : IsPosPot R.A Θ) (hL : IsPotential R.A L)
    (hs : IsSection R.A L s) (hsnc : IsSNC R.A L s mb Wb) (hle : ∀ x, logNormSec L s x ≤ 0) {σ : Type} [Fintype σ]
    (A : ℝ → σ → HermLine J) (M : ℝ → HermLine J) (m : σ → ℤ) (n : Fin d → σ → ℤ) (q : Fin d → Prop) [DecidablePred q]
    (hq : ∀ k, q k → n k = m) (hA : ∀ i, Tame R Θ L s fun t => A t i) (hM : Tame R Θ L s M) {f g : MRing J}
    {w : ℝ → ((Σ k, J k) → ℂ) → ℝ} {C : ℝ}
    (hw : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsLineIso P (Top.combLine (A t) m).a (M t).a f g ∧
      IsDefectOn P (mcPts P) f g (Top.combLine (A t) m) (M t) (w t) ∧
      ∀ x ∉ bdry s, |w t (R.lift x x)| ≤ C * Real.log (rW L s x))
    (hw0 : ∀ K' ⊆ (bdry s)ᶜ, IsCompact K' →
      TendstoUniformlyOn (fun t x => w t (R.lift x x)) (fun _ => 0) (𝓝[>] 0) K') :
    Tendsto (fun t => II K J P d (fun k => if q k then M t else Top.combLine (A t) (n k)) -
      II K J P d fun k => Top.combLine (A t) (n k)) (𝓝[>] 0) (𝓝 0) := by
  classical
  subst hd
  have hAs : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, IsSmoothHerm (A t i) := eventually_all.2 fun i => by
    obtain ⟨_, _, -, h⟩ := hA i
    exact h.mono fun t ht => ht.1
  have hMs : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (M t) := by
    obtain ⟨_, _, -, h⟩ := hM
    exact h.mono fun t ht => ht.1
  have hc : ∀ t, (∀ i, IsSmoothHerm (A t i)) → ∀ r, IsSmoothHerm (Top.combLine (A t) r) := fun t h r =>
    (_root_.GlobalTheory.CompanionTheory.Ar.Top.combLine_smooth_conj K J σ (A t) r).1 h
  let l : ℝ → Option (Option σ) → HermLine J := fun t o => o.elim (Top.combLine (A t) m) fun o' => o'.elim (M t) (A t)
  let ν : (σ → ℤ) → Option (Option σ) → ℤ := fun r o => o.elim 0 fun o' => o'.elim 0 r
  have hν : ∀ t r, Top.combLine (l t) (ν r) = Top.combLine (A t) r := fun t r => by
    refine OneSlot.hermLine_ext ?_ (funext fun z => ?_)
    · show ∑ j, ν r j • (l t j).a = ∑ j, r j • (A t j).a
      simp [Fintype.sum_option, ν, l]
    · show ∏ j, (l t j).h z ^ ν r j = ∏ j, (A t j).h z ^ r j
      simp [Fintype.prod_option, ν, l]
  have hstep : ∀ i : Fin (e + 1), Tendsto (fun t =>
      II K J P (e + 1) (fun j => if j < i then Top.combLine (A t) (n j) else
        if q j then M t else Top.combLine (A t) (n j)) -
      II K J P (e + 1) (fun j => if j ≤ i then Top.combLine (A t) (n j) else
        if q j then M t else Top.combLine (A t) (n j))) (𝓝[>] 0) (𝓝 0) := by
    intro i
    by_cases hi : q i
    swap
    · refine tendsto_const_nhds.congr fun t => (sub_eq_zero.2 (congrArg _ (funext fun j => ?_))).symm
      rcases lt_trichotomy j i with h | rfl | h
      · simp [h, h.le]
      · simp [hi]
      · simp [h.not_gt, h.not_ge]
    let μ : Fin e → Option (Option σ) → ℤ := fun k =>
      if ¬ i.succAbove k < i ∧ q (i.succAbove k) then Pi.single (some none) 1 else ν (n (i.succAbove k))
    have hμ0 : ∀ k, μ k none = 0 := fun k => by
      simp only [μ]
      split_ifs
      · simp
      · rfl
    have hμ : ∀ t k, Top.combLine (l t) (μ k) = if i.succAbove k < i then Top.combLine (A t) (n (i.succAbove k)) else
        if q (i.succAbove k) then M t else Top.combLine (A t) (n (i.succAbove k)) := fun t k => by
      simp only [μ]
      by_cases h1 : i.succAbove k < i
      · simp [h1, hν]
      · by_cases h2 : q (i.succAbove k)
        · simp only [h1, h2, not_false_eq_true, and_self, if_true, if_false]
          exact comb_single _ _
        · simp [h1, h2, hν]
    have hterm : ∀ u : Fin e → Option (Option σ), Tendsto (fun t => (∏ k, (μ k (u k) : ℝ)) *
        (II K J P (e + 1) (Fin.snoc (fun k => l t (u k)) (M t)) -
          II K J P (e + 1) (Fin.snoc (fun k => l t (u k)) (Top.combLine (A t) m)))) (𝓝[>] 0) (𝓝 0) := by
      intro u
      by_cases hu : ∃ k, u k = none
      · obtain ⟨k, hk⟩ := hu
        rw [Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk, hμ0, Int.cast_zero])]
        simp
      · have h := position_zero (hII.1 K J) R hP hΘ hΘp hL hs hsnc hle (fun k t => l t (u k)) (fun k => by
          rcases hk : u k with _ | _ | a
          · exact absurd ⟨k, hk⟩ hu
          · exact hM
          · exact hA a) ((hAs.and hMs).mono fun t ht => ⟨hc t ht.1 m, ht.2⟩) hw hw0
        simpa using h.const_mul (∏ k, (μ k (u k) : ℝ))
    have hsum := tendsto_finsetSum Finset.univ fun u (_ : u ∈ Finset.univ) => hterm u
    simp only [Finset.sum_const_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [hAs, hMs] with t h1 h2
    have hl : ∀ o, IsSmoothHerm (l t o) := by
      rintro (_ | _ | a)
      exacts [hc t h1 m, h2, h1 a]
    have s₁ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.movePositionToLast K J (II K J) (hII.1 K J) P e (fun j => if j < i then Top.combLine (A t) (n j) else
      if q j then M t else Top.combLine (A t) (n j)) i hP fun j => by
        split_ifs
        exacts [hc t h1 _, h2, hc t h1 _]
    have s₂ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.movePositionToLast K J (II K J) (hII.1 K J) P e (fun j => if j ≤ i then Top.combLine (A t) (n j) else
      if q j then M t else Top.combLine (A t) (n j)) i hP fun j => by
        split_ifs
        exacts [hc t h1 _, h2, hc t h1 _]
    have hiff : ∀ k : Fin e, i.succAbove k ≤ i ↔ i.succAbove k < i := fun k =>
      ⟨fun h => lt_of_le_of_ne h (Fin.succAbove_ne i k), le_of_lt⟩
    simp only [lt_irrefl, le_refl, hi, if_true, if_false, hiff, hq i hi, ← hμ] at s₁ s₂
    rw [s₁, s₂]
    have e₁ := ii_comb_snoc hII hP (l t) hl μ (some none)
    have e₂ := ii_comb_snoc hII hP (l t) hl μ none
    refine Eq.trans ?_ (congrArg₂ (· - ·) e₁ e₂).symm
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => mul_sub _ _ _
  have hsum := tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) => hstep i
  simp only [Finset.sum_const_zero] at hsum
  refine hsum.congr fun t => ?_
  exact (_root_.GlobalTheory.CompanionTheory.Telescope.telescope_fin_positions (HermLine J) (e + 1) (II K J P (e + 1)) _ _).symm

theorem replace : Replace := by
  intro _ II hII K _ J _ P B e a b R Θ L s nb mb Wb σ _ A M m n f g w C hab hP hΘ hΘp hL hs hsnc hle hA hM hw hw0
  have h := replace_gen hII hab R hP hΘ hΘp hL hs hsnc hle A M m (Fin.append (fun _ : Fin a => m) n)
    (fun k => (k : ℕ) < a) (fun k => by
      refine Fin.addCases (fun k _ => ?_) (fun k hk => ?_) k
      · simp
      · simp at hk) hA hM hw hw0
  refine h.congr fun t => ?_
  congr 2
  · funext k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> simp
  · funext k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> simp

end LevelTowerAlt.Comparison₂
end
end

