module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0048
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0050
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0047
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0052
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalResolutionOpen
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact

theorem chart_points : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ w ∈ pD ε V, (∀ τ, IsBlockDiag j (pH keep h ε τ w) ∧ (pH keep h ε τ w).det ≠ 0) ∧ pBase M v (pPhi M F keep v bl h ε w) = bl (pB ε w) ∧ ∀ p k, keep p → M.blk p = some k → ∀ m : ι k, upV v (pPhi M F keep v bl h ε w) ⟨k, m⟩ = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (bl (pB ε w)) * minorIJ (pH keep h ε p.1 w) I (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hc w hw
  obtain ⟨hbm, hran, -, -, -, -, hh⟩ := hc
  have key : ∀ q : Σ k, ι k, q.1 ∈ Set.range κ → upV v (pPhi M F keep v bl h ε w) q =
      flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w) q := by
    intro q hq
    obtain ⟨q', rfl⟩ := hbm.2.2.2 q hq
    rw [upV_apply hbm.2.1]
    rfl
  refine ⟨fun τ => ⟨?_, ?_⟩, ?_, fun p k hk hp m => ?_⟩
  · exact isBlockDiag_mul (hh τ).1 (WMan.Exact.lowMat_isBlockDiag _ _)
  · rw [pH, Matrix.det_mul, pMat, WMan.Exact.lowMat_det, mul_one]
    exact (hh τ).2
  · funext q
    obtain ⟨k, m⟩ := q
    show upV v (pPhi M F keep v bl h ε w) ⟨k.1, m⟩ = _
    rw [key ⟨k.1, m⟩ ((hran k.1).2 (Or.inl k.2))]
    exact WMan.Exact.flagZ_base k m
  · rw [key ⟨k, m⟩ ((hran k).2 (Or.inr ⟨p, hk, hp⟩))]
    exact WMan.Exact.flagZ_step hp m

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalResolutionRegular
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Holo

open GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo

section Flag

variable {Ψ : Type} {N j n e : ℕ}

theorem analytic_pMat (keep : Ψ × Fin N → Prop) (s : Set (Fin e → ℂ)) (ε : Fin n ⊕ PIdx j keep ≃ Fin e)
    (τ : Ψ) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => pMat keep (pL ε w) τ a b) s := by
  unfold pMat lowMat
  by_cases hc : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
  · simp only [hc, dite_true]
    by_cases hs : Sep keep (⟨(τ, a, b), hc⟩ : LowIdx Ψ N j)
    · simp only [cExt, hs, dite_true, pL]
      exact analytic_coord _
    · simp only [cExt, hs, dite_false]
      exact analyticOnNhd_const
  · simp only [hc, dite_false]
    exact analyticOnNhd_const

theorem analytic_pH (keep : Ψ × Fin N → Prop) (s : Set (Fin e → ℂ)) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (ε : Fin n ⊕ PIdx j keep ≃ Fin e) (τ : Ψ) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => pH keep h ε τ w a b) s := by
  unfold pH
  exact analytic_mul_entry (fun _ => h τ) _ (fun _ _ => analyticOnNhd_const)
    (analytic_pMat keep s ε τ) a b

theorem analytic_pB {Λ : Type} (ε : Fin n ⊕ Λ ≃ Fin e) (V : Set (Fin n → ℂ)) :
    AnalyticOnNhd ℂ (pB ε) (pD ε V) := by
  have : pB ε = ⇑(ContinuousLinearMap.pi (R := ℂ) fun i : Fin n =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) (ε (Sum.inl i))) := by
    funext w i
    rfl
  rw [this]
  exact fun w _ => ContinuousLinearMap.analyticAt _ w

end Flag

theorem pPhi_holo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ p, AnalyticOnNhd ℂ (fun w => pPhi M F keep v bl h ε w p) (pD ε V) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hc p
  obtain ⟨-, -, -, hb, -⟩ := hc
  obtain ⟨-, -, hbl, hval, -⟩ := hb
  have hmap : Set.MapsTo (pB ε) (pD ε V) V := fun w hw => hw
  have hzb : ∀ q, AnalyticOnNhd ℂ (fun w => bl (pB ε w) q) (pD ε V) := fun q =>
    (hbl q).comp (analytic_pB ε V) hmap
  have hv : ∀ q I, AnalyticOnNhd ℂ (fun w => valAt M.x (F.u q I) (bl (pB ε w))) (pD ε V) := fun q I =>
    (hval q I).comp (analytic_pB ε V) hmap
  exact analytic_flagZ M F (fun w => bl (pB ε w)) (fun w τ' => pH keep h ε τ' w) hzb hv
    (fun τ' => analytic_pH keep _ h ε τ') (v p)

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Holo
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftSystemRealStructure
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

section Holo

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem pot_holoOn_mono {V W : Set X} {g : X → ℂ} (h : A.HoloOn V g) (hW : W ⊆ V) :
    A.HoloOn W g :=
  fun j w hw => h j w ⟨hw.1, hW hw.2⟩

theorem pot_holoOn_continuousOn {V : Set X} (hV : IsOpen V) {g : X → ℂ} (h : A.HoloOn V g) :
    ContinuousOn g V := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have hw : A.chart j y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' V :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hy⟩
  have h1 := (h j _ hw).continuousAt
  have h2 : ContinuousAt (A.chart j) y := (A.chart j).continuousAt hj
  have h3 : ContinuousAt (fun y' => (g ∘ (A.chart j).symm) (A.chart j y')) y :=
    ContinuousAt.comp (g := g ∘ (A.chart j).symm) h1 h2
  refine (h3.congr ?_).continuousWithinAt
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y' hy'
  simp [(A.chart j).left_inv hy']

theorem pot_holoOn_sub_add {V : Set X} {g₁ g₂ g₃ : X → ℂ} (h₁ : A.HoloOn V g₁)
    (h₂ : A.HoloOn V g₂) (h₃ : A.HoloOn V g₃) :
    A.HoloOn V (fun y => g₁ y - g₂ y + g₃ y) :=
  fun j w hw => ((h₁ j w hw).sub (h₂ j w hw)).add (h₃ j w hw)

theorem pot_holoOn_div {V : Set X} {g₁ g₂ : X → ℂ} (h₁ : A.HoloOn V g₁) (h₂ : A.HoloOn V g₂)
    (hne : ∀ y ∈ V, g₂ y ≠ 0) : A.HoloOn V (fun y => g₁ y / g₂ y) :=
  fun j w hw => (h₁ j w hw).div (h₂ j w hw) (hne _ hw.2)

theorem pot_holoOn_sum_log {K : Type} [Fintype K] {V : Set X} {g : K → X → ℂ} (m : K → ℤ)
    (r : K → ℝ) (h : ∀ k, A.HoloOn V (g k)) (hs : ∀ k, ∀ y ∈ V, g k y ∈ Complex.slitPlane) :
    A.HoloOn V (fun y => ∑ k, (m k : ℂ) * (Complex.log (g k y) + (r k : ℂ))) := by
  intro j w hw
  have : ∀ k, AnalyticAt ℂ (fun z => (m k : ℂ) *
      (Complex.log (g k ((A.chart j).symm z)) + (r k : ℂ))) w := fun k =>
    analyticAt_const.mul ((AnalyticAt.clog (h k j w hw) (hs k _ hw.2)).add analyticAt_const)
  exact Finset.analyticAt_fun_sum _ fun k _ => this k

end Holo

theorem pot_re_sum_log {K : Type} [Fintype K] (m : K → ℤ) (u v : K → ℂ) (hu : ∀ k, u k ≠ 0)
    (hv : ∀ k, v k ≠ 0) :
    (∑ k, (m k : ℂ) * (Complex.log (u k / v k) + ((Real.log ‖v k‖ : ℝ) : ℂ))).re =
      ∑ k, (m k : ℝ) * Real.log ‖u k‖ := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (Complex.log (u k / v k) + ((Real.log ‖v k‖ : ℝ) : ℂ)).re = Real.log ‖u k‖ := by
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.2 (hu k)) (norm_ne_zero_iff.2 (hv k))]
    ring
  simp [Complex.mul_re, h1]

theorem pot_log_h_conj {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (f : HermLine ι)
    (hf : IsConjInvariantH f) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) {a : K → ℂ}
    (ha : ∀ k, a k ≠ 0) :
    Real.log (f.h (fun p => a p.1 * cj z p)) - Real.log (f.h z) =
      ∑ k, (f.a k : ℝ) * Real.log ‖a k‖ := by
  have hP : ∀ k ∈ (Finset.univ : Finset K), ‖a k‖ ^ f.a k ≠ 0 := fun k _ =>
    (zpow_pos (norm_pos_iff.mpr (ha k)) _).ne'
  have hP' : (∏ k, ‖a k‖ ^ f.a k) ≠ 0 := Finset.prod_ne_zero_iff.2 hP
  rw [f.smul a (cj z) ha, show f.h (cj z) = f.h z from hf z,
    Real.log_mul hP' (f.pos z hz).ne', Real.log_prod hP]
  simp [Real.log_zpow]

theorem pot_conj_pluriharmonic : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∀ (c : X → X), (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) → Continuous c → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → ∀ (f : HermLine ι), IsConjInvariantH f → ∀ (th : LocPot X), (∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, Real.log (f.h (lift x y)) - th.φ x y = (G y).re) → ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, th.φ (c x) (c y) - th.φ x y = (G y).re := by
  intro K _ ι _ e X _ A P U lift hL c horb hcc hanti f hf th hth x
  obtain ⟨hUo, hUm, hUh, hUpts, hUor, -, -, -⟩ := hL
  choose i hi using (hUpts x x (hUm x)).1
  obtain ⟨V₁, hV₁o, hxV₁, G₁, hG₁, hφ₁⟩ := hth x
  obtain ⟨V₂, hV₂o, hxV₂, G₂, hG₂, hφ₂⟩ := hth (c x)

  have horbit : ∀ y ∈ U x, c y ∈ U (c x) → ∃ a : K → ℂ, (∀ k, a k ≠ 0) ∧
      lift (c x) (c y) = fun p => a p.1 * cj (lift x y) p := fun y hy hcy =>
    sameOrbit_trans (sameOrbit_trans (hUor (c x) (c y) (c y) ⟨hcy, hUm (c y)⟩) (horb y))
      (sameOrbit_cj (hUor y x y ⟨hUm y, hy⟩))

  let b : K → X → ℂ := fun k y =>
    starRingEnd ℂ (lift (c x) (c y) ⟨k, i k⟩) / lift x y ⟨k, i k⟩
  let D : K → Set X := fun k => U x ∩ (fun y => lift x y ⟨k, i k⟩) ⁻¹' {0}ᶜ
  have hDo : ∀ k, IsOpen (D k) := fun k =>
    (pot_holoOn_continuousOn (hUo x) (hUh x _)).isOpen_inter_preimage (hUo x) isOpen_compl_singleton
  let W₁ : Set X := (U x ∩ c ⁻¹' U (c x)) ∩ ⋂ k, D k
  have hW₁o : IsOpen W₁ :=
    ((hUo x).inter ((hUo (c x)).preimage hcc)).inter (isOpen_iInter_of_finite hDo)
  have hxW₁ : x ∈ W₁ :=
    ⟨⟨hUm x, hUm (c x)⟩, Set.mem_iInter.2 fun k => ⟨hUm x, hi k⟩⟩
  have hden : ∀ y ∈ W₁, ∀ k, lift x y ⟨k, i k⟩ ≠ 0 := fun y hy k =>
    (Set.mem_iInter.1 hy.2 k).2

  have hba : ∀ y ∈ W₁, ∀ a : K → ℂ, lift (c x) (c y) = (fun p => a p.1 * cj (lift x y) p) →
      ∀ k, b k y = starRingEnd ℂ (a k) := fun y hy a ha k => by
    change starRingEnd ℂ (lift (c x) (c y) ⟨k, i k⟩) / lift x y ⟨k, i k⟩ = _
    rw [ha]
    simp only [cj, map_mul, Complex.conj_conj]
    exact mul_div_cancel_right₀ _ (hden y hy k)
  have hbne : ∀ y ∈ W₁, ∀ k, b k y ≠ 0 := fun y hy k => by
    obtain ⟨a, ha, hl⟩ := horbit y hy.1.1 hy.1.2
    rw [hba y hy a hl k]
    simpa using ha k
  have hbH : ∀ k, A.HoloOn W₁ (b k) := fun k =>
    pot_holoOn_div
      (pot_holoOn_mono (GlobalTheory.T.holomorphic_conjugate_pullback c hcc hanti (hUh (c x) ⟨k, i k⟩)) fun y hy => hy.1.2)
      (pot_holoOn_mono (hUh x ⟨k, i k⟩) fun y hy => hy.1.1) fun y hy => hden y hy k
  have hqH : ∀ k, A.HoloOn W₁ (fun y => b k y / b k x) := fun k =>
    pot_holoOn_div (hbH k) (fun j w _ => analyticAt_const) fun _ _ => hbne x hxW₁ k
  let B : K → Set X := fun k => W₁ ∩ (fun y => b k y / b k x) ⁻¹' Metric.ball 1 1
  have hBo : ∀ k, IsOpen (B k) := fun k =>
    (pot_holoOn_continuousOn hW₁o (hqH k)).isOpen_inter_preimage hW₁o Metric.isOpen_ball
  let W₂ : Set X := W₁ ∩ ⋂ k, B k
  let V : Set X := (W₂ ∩ V₁) ∩ c ⁻¹' V₂
  have hVo : IsOpen V :=
    ((hW₁o.inter (isOpen_iInter_of_finite hBo)).inter hV₁o).inter (hV₂o.preimage hcc)
  have hVW : V ⊆ W₁ := fun y hy => hy.1.1.1
  have hxV : x ∈ V := by
    refine ⟨⟨⟨hxW₁, Set.mem_iInter.2 fun k => ⟨hxW₁, ?_⟩⟩, hxV₁⟩, hxV₂⟩
    simp [div_self (hbne x hxW₁ k)]
  have hslit : ∀ k, ∀ y ∈ V, b k y / b k x ∈ Complex.slitPlane := fun k y hy => by
    have h1 : b k y / b k x ∈ Metric.ball (1 : ℂ) 1 := (Set.mem_iInter.1 hy.1.1.2 k).2
    have h2 : ‖b k y / b k x - 1‖ < 1 := by simpa [dist_eq_norm] using h1
    simpa using Complex.mem_slitPlane_of_norm_lt_one h2
  refine ⟨V, hVo, hxV,
    fun y => G₁ y - starRingEnd ℂ (G₂ (c y)) +
      ∑ k, (f.a k : ℂ) * (Complex.log (b k y / b k x) + ((Real.log ‖b k x‖ : ℝ) : ℂ)), ?_, ?_⟩
  · refine pot_holoOn_sub_add (pot_holoOn_mono hG₁ fun y hy => hy.1.2)
      (pot_holoOn_mono (GlobalTheory.T.holomorphic_conjugate_pullback c hcc hanti hG₂) fun y hy => hy.2) ?_
    exact pot_holoOn_sum_log f.a _ (fun k => pot_holoOn_mono (hqH k) hVW) fun k => hslit k
  · intro y hy
    have hyW := hVW hy
    obtain ⟨a, ha, hl⟩ := horbit y hyW.1.1 hyW.1.2
    have e₁ := hφ₁ y hy.1.2
    have e₂ := hφ₂ (c y) hy.2
    have e₃ := pot_log_h_conj f hf (hUpts x y hyW.1.1).1 ha
    rw [← hl] at e₃
    have e₄ := pot_re_sum_log f.a (fun k => b k y) (fun k => b k x) (hbne y hyW) (hbne x hxW₁)
    have e₅ : ∑ k, (f.a k : ℝ) * Real.log ‖b k y‖ = ∑ k, (f.a k : ℝ) * Real.log ‖a k‖ :=
      Finset.sum_congr rfl fun k _ => by rw [hba y hyW a hl k, RCLike.norm_conj]
    simp only [Complex.add_re, Complex.sub_re, Complex.conj_re]
    rw [e₄, e₅, ← e₃]
    linarith

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicLiftRealisation
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_comp_of_holoOn {D e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) {V : Set (Fin e → ℂ)}
    {Y : Set X} {g : X → ℂ} (hg : A.HoloOn Y g) {h : (Fin e → ℂ) → X} {z : Fin e → ℂ}
    (hV : V ∈ 𝓝 z) (hc : ContinuousOn h V)
    (ha : ∀ k, AnalyticOnNhd ℂ (A.chart k ∘ h) (V ∩ h ⁻¹' (A.chart k).source)) (hz : h z ∈ Y) :
    AnalyticAt ℂ (g ∘ h) z := by
  obtain ⟨k, hk⟩ := A.cover (h z)
  have hcz : ContinuousAt h z := hc.continuousAt hV
  have h1 : AnalyticAt ℂ (A.chart k ∘ h) z := ha k z ⟨mem_of_mem_nhds hV, hk⟩
  have h2 : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h) z) := by
    refine hg k _ ⟨(A.chart k).map_source hk, ?_⟩
    simpa [Set.mem_preimage, (A.chart k).left_inv hk] using hz
  have h3 : AnalyticAt ℂ ((g ∘ (A.chart k).symm) ∘ (A.chart k ∘ h)) z := h2.comp h1
  refine h3.congr ?_
  filter_upwards [hcz.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)] with u hu
  simp [(A.chart k).left_inv hu]

theorem ref_pot_along_exact_family : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (a : σ) (e : ℕ) (V : Set (Fin e → ℂ)) (ΦY : (Fin e → ℂ) → S.X) (zex : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (z : Fin e → ℂ), Re.J = ⊤ → Re.deg = 1 → Re.br = ∅ → IsOpen V → z ∈ V → (∀ q, AnalyticOnNhd ℂ (fun u => zex u q) V) → (∀ u ∈ V, zex u ∈ mcPts P) → (∀ u ∈ V, ∀ x₀, Re.π x₀ = ΦY u → SameOrbit (Re.R.lift x₀ x₀) (zex u)) → ∃ Hh : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, (S.th a).φ (ΦY z) (ΦY z') = Real.log ((Re.ref a).h (zex z')) + (Hh z').re := by
  intro K _ ι _ D σ S P Re a e V ΦY zex z hJ hdeg hbr hV hzV hana hmc hex
  have hbij : Function.Bijective Re.π := realis_bijective_of_degree_one K ι D σ S P Re hdeg hbr
  set h : (Fin e → ℂ) → Re.R.X := fun u => Function.surjInv hbij.2 (ΦY u) with hdef
  have hπ : ∀ u, Re.π (h u) = ΦY u := fun u => Function.surjInv_eq hbij.2 (ΦY u)
  have hSO : ∀ u ∈ V, SameOrbit (Re.R.lift (h u) (h u)) (zex u) := fun u hu => hex u hu (h u) (hπ u)
  obtain ⟨hc, hch⟩ := holo_of_lift_orbit_top K ι P Re.J D e Re.R V zex h hJ hV hana hmc hSO
  have hVn : V ∈ 𝓝 z := hV.mem_nhds hzV
  have hcz : ContinuousAt h z := hc.continuousAt hVn
  obtain ⟨W, hW, hxW, G, hG, hGeq⟩ := Re.ref_pot a (h z) (Set.mem_univ _)
  have hGh : AnalyticAt ℂ (G ∘ h) z := analyticAt_comp_of_holoOn Re.R.A hG hVn hc hch hxW
  have hxU : h z ∈ Re.R.U (h z) := Re.R.mem_U _

  have hi : ∀ k, ∃ i, zex z ⟨k, i⟩ ≠ 0 := (hmc z hzV).1
  choose i hi using hi
  set c : K → (Fin e → ℂ) → ℂ := fun k u => Re.R.lift (h z) (h u) ⟨k, i k⟩ / zex u ⟨k, i k⟩ with hcdef
  have hcan : ∀ k, AnalyticAt ℂ (c k) z := fun k =>
    AnalyticAt.div (analyticAt_comp_of_holoOn Re.R.A (Re.R.holo (h z) ⟨k, i k⟩) hVn hc hch hxU)
      (hana _ z hzV) (hi k)
  have hcz0 : ∀ k, c k z ≠ 0 := by
    intro k
    obtain ⟨d, hd, hdz⟩ := hSO z hzV
    have : Re.R.lift (h z) (h z) ⟨k, i k⟩ = d k * zex z ⟨k, i k⟩ := congrFun hdz ⟨k, i k⟩
    simp only [hcdef, this]
    exact div_ne_zero (mul_ne_zero (hd k) (hi k)) (hi k)
  have hL : ∀ k, ∃ Lk : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Lk z ∧ ∀ᶠ z' in 𝓝 z, Real.log ‖c k z'‖ = (Lk z').re :=
    fun k => log_norm_eventually_eq_re_analyticAt e (c k) z (hcan k) (hcz0 k)
  choose L hLan hLeq using hL
  refine ⟨fun u => (∑ k, (((Re.ref a).a k : ℤ) : ℂ) * L k u) - G (h u), ?_, ?_⟩
  · refine AnalyticAt.sub ?_ hGh
    exact Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul (hLan k)
  · have hne : ∀ᶠ u in 𝓝 z, ∀ k, zex u ⟨k, i k⟩ ≠ 0 :=
      eventually_all.2 fun k => (hana _ z hzV).continuousAt.eventually_ne (hi k)
    filter_upwards [hVn, hne, eventually_all.2 hLeq, hcz.preimage_mem_nhds (hW.mem_nhds hxW),
      hcz.preimage_mem_nhds ((Re.R.isOpen_U (h z)).mem_nhds hxU)] with u huV hune huL huW huU
    have hcompat := Re.R.compat (h z) (h u) (h u) ⟨huU, Re.R.mem_U _⟩
    obtain ⟨d₁, hd₁, e₁⟩ := hcompat
    obtain ⟨d₂, hd₂, e₂⟩ := hSO u huV
    have hlift : Re.R.lift (h z) (h u) = fun p => (d₁ p.1 * d₂ p.1) * zex u p := by
      funext p
      rw [congrFun e₁ p, congrFun e₂ p, mul_assoc]
    have hck : ∀ k, c k u = d₁ k * d₂ k := by
      intro k
      simp only [hcdef, hlift]
      field_simp [hune k]
    have hlift' : Re.R.lift (h z) (h u) = fun p => c p.1 u * zex u p := by
      rw [hlift]; funext p; rw [hck]
    have hcne : ∀ k, c k u ≠ 0 := fun k => by
      rw [hck]; exact mul_ne_zero (hd₁ k) (hd₂ k)
    have hsm := (Re.ref a).smul (fun k => c k u) (zex u) hcne
    have hpos := (Re.ref a).pos (zex u) (hmc u huV).1
    have hlog : Real.log ((Re.ref a).h (Re.R.lift (h z) (h u))) =
        (∑ k, ((Re.ref a).a k : ℝ) * Real.log ‖c k u‖) + Real.log ((Re.ref a).h (zex u)) := by
      rw [hlift', hsm, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ =>
        zpow_ne_zero _ (norm_ne_zero_iff.2 (hcne k))) hpos.ne', Real.log_prod]
      · simp only [Real.log_zpow]
      · exact fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hcne k))
    have hG' : Real.log ((Re.ref a).h (Re.R.lift (h z) (h u))) - (S.th a).φ (ΦY z) (ΦY u) = (G (h u)).re := by
      have := hGeq (h u) huW
      simpa only [potOf, LocPot.pullback, hπ] using this
    have hre : ((∑ k, (((Re.ref a).a k : ℤ) : ℂ) * L k u) - G (h u)).re =
        (∑ k, ((Re.ref a).a k : ℝ) * Real.log ‖c k u‖) - (G (h u)).re := by
      rw [Complex.sub_re, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [huL k]
      simp
    rw [hre]
    linarith

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMongeAmpereNormalizedStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_sine_monge_ampere_normalized : GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (d k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → ∀ (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ContDiffAt ℝ 2 α y → G y = 1 → (∀ p q, fderiv ℝ (fun y' => G y' p q) y = 0) → (∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y))) = 2 * ReciprocityTheory.ChartRestriction.G.AI.kappa k * ∫ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.fibre_integral_normal | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.fibre_integral_normal | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.fibre_integral_normal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NefThresholdGapCondition
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold

theorem ent_of_lt {T : Type} [Fintype T] {N : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (τ : T) {i : ℕ} (h : i < N) :
    GlobalTheory.CompanionTheory.Ar.Top.ent mu τ i = mu τ ⟨i, h⟩ := by
  unfold GlobalTheory.CompanionTheory.Ar.Top.ent
  rw [dif_pos h]

theorem abs_le_norm {T : Type} [Fintype T] {N : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (τ : T) (i : Fin N) :
    |mu τ i| ≤ ‖mu‖ := by
  have h1 : ‖mu τ i‖ ≤ ‖mu τ‖ := norm_le_pi_norm (mu τ) i
  have h2 : ‖mu τ‖ ≤ ‖mu‖ := norm_le_pi_norm mu τ
  rw [Real.norm_eq_abs] at h1
  exact h1.trans h2

theorem gapCond_of_threshold {T : Type} [Fintype T] {N j p : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N)
    (hp : 2 < p) (hj : 1 ≤ j) (hjN : j < N) (hd : GlobalTheory.CompanionTheory.Ar.Top.Dominant mu)
    (ht : GlobalTheory.CompanionTheory.Ar.Top.NefThreshold j p mu) :
    GapCond p j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) := by
  unfold GlobalTheory.CompanionTheory.Ar.Top.NefThreshold GlobalTheory.CompanionTheory.Ar.Top.gap at ht
  unfold GlobalTheory.CompanionTheory.Ar.Top.Dominant at hd
  have hp' : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp
    linarith
  unfold GapCond
  refine ⟨?_, ‖mu‖, 4 * (Fintype.card T) * ‖mu‖ / ((p : ℝ) - 2), ?_, ?_, ?_⟩
  · intro τ i hi hiN
    have h1 : i < N := by omega
    have h0 : i - 1 < N := by omega
    simp only [Nat.add_sub_cancel]
    rw [ent_of_lt mu τ h1, ent_of_lt mu τ h0]
    exact hd τ ⟨i - 1, h0⟩ ⟨i, h1⟩ (Fin.mk_le_mk.2 (by omega))
  · intro τ i hi hiN
    have h0 : i - 1 < N := by omega
    simp only
    rw [ent_of_lt mu τ h0]
    exact abs_le_norm mu τ _
  · intro τ
    simp only [Nat.add_sub_cancel]
    rw [div_le_iff₀ hp']
    linarith [ht τ, mul_comm ((p : ℝ) - 2) (GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (j - 1) - GlobalTheory.CompanionTheory.Ar.Top.ent mu τ j)]
  · have e : ((p : ℝ) - 2) * (4 * (Fintype.card T) * ‖mu‖ / ((p : ℝ) - 2)) = 4 * (Fintype.card T) * ‖mu‖ := by
      field_simp
    exact e.ge

theorem lmuNum_eq_sum {T : Type} [Fintype T] {N j : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N)
    (x : T × Fin N → ℝ) (w l : T → ℕ → ℝ) (hjN : j < N)
    (hx : ∀ τ (i : Fin N), (i : ℕ) < j → x (τ, i) = w τ (i + 1) - w τ i)
    (hy : ∀ τ (i : Fin N), j ≤ (i : ℕ) → x (τ, i) = -(l τ (N - 1 - i + 1) - l τ (N - 1 - i))) :
    lmuNum j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) w l = ∑ r : T × Fin N, -mu r.1 r.2 * x r := by
  classical
  unfold lmuNum
  set xx : T → ℕ → ℝ := fun τ i => if h : i < N then x (τ, ⟨i, h⟩) else 0 with hxx
  have hrow : ∀ τ, ∑ i : Fin N, -mu τ i * x (τ, i) =
      ∑ i ∈ Finset.range N, -GlobalTheory.CompanionTheory.Ar.Top.ent mu τ i * xx τ i := by
    intro τ
    rw [← Fin.sum_univ_eq_sum_range (fun i => -GlobalTheory.CompanionTheory.Ar.Top.ent mu τ i * xx τ i) N]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hxx, dif_pos i.isLt, ent_of_lt mu τ i.isLt]
  rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [hrow τ, ← Finset.sum_range_add_sum_Ico _ hjN.le, Finset.sum_Ico_eq_sum_range, neg_add]
  congr 1
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i < j := Finset.mem_range.1 hi
    have hiN : i < N := by omega
    have hx' := hx τ ⟨i, hiN⟩ hij
    simp only [hxx, dif_pos hiN, Nat.add_sub_cancel, hx']
    ring
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmj : m < N - j := Finset.mem_range.1 hm
    have hiN : j + m < N := by omega
    have hy' := hy τ ⟨j + m, hiN⟩ (by simp)
    have e1 : N - 1 - (j + m) + 1 = N - j - m := by omega
    have e2 : N - 1 - (j + m) = N - j - m - 1 := by omega
    simp only [hxx, dif_pos hiN, Nat.add_sub_cancel, hy']
    rw [e1, e2]
    ring

theorem gapCond_and_lmuNum : ∀ (T : Type) [Fintype T] (N j p : ℕ) (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (x : T × Fin N → ℝ) (w l : T → ℕ → ℝ), 2 < p → 1 ≤ j → j < N → GlobalTheory.CompanionTheory.Ar.Top.Dominant mu → GlobalTheory.CompanionTheory.Ar.Top.NefThreshold j p mu → (∀ τ (i : Fin N), (i : ℕ) < j → x (τ, i) = w τ (i + 1) - w τ i) → (∀ τ (i : Fin N), j ≤ (i : ℕ) → x (τ, i) = -(l τ (N - 1 - i + 1) - l τ (N - 1 - i))) → GapCond p j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) ∧ lmuNum j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) w l = ∑ r : T × Fin N, -mu r.1 r.2 * x r := by
  intro T _ N j p mu x w l hp hj hjN hd ht hx hy
  exact ⟨gapCond_of_threshold mu hp hj hjN hd ht, lmuNum_eq_sum mu x w l hjN hx hy⟩

end GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold
end

