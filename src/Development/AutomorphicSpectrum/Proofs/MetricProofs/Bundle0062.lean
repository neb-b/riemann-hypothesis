module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0047
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0055
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJEqSubmatrix
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0011
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackStatementHolds
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

section PullTop

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isPsh_of_phi_eq {A : FinHolAtlas e X} {P Q : LocPot X} (hQ : IsPotential A Q)
    (hφ : P.φ = Q.φ) (hP : IsPsh A P) : IsPsh A Q := by
  intro x j y hy w
  obtain ⟨W, hW, hzW, G, hG, hGe⟩ :=
    hQ.2 x ((A.chart j).symm y) ((A.chart j).symm y) ⟨hy.2, Q.mem_U _⟩
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy.1, hzW⟩
  have ho : IsOpen ((A.chart j).target ∩
      (A.chart j).symm ⁻¹' (W ∩ Q.U x ∩ Q.U ((A.chart j).symm y))) :=
    (A.chart j).isOpen_inter_preimage_symm ((hW.inter (Q.isOpen_U x)).inter (Q.isOpen_U _))
  have hev : (Q.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun v =>
      (Q.φ ((A.chart j).symm y) ∘ (A.chart j).symm) v + 1 * ((G ∘ (A.chart j).symm) v).re := by
    filter_upwards [ho.mem_nhds ⟨hy.1, ⟨hzW, hy.2⟩, Q.mem_U _⟩] with v hv
    have := hGe _ hv.2
    simp only [Function.comp_apply]
    linarith
  have ho2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U ((A.chart j).symm y)) :=
    (A.chart j).isOpen_inter_preimage_symm (Q.isOpen_U _)
  have h2 : ContDiffAt ℝ 2 (Q.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
    ((hQ.1 _ j).contDiffAt (ho2.mem_nhds ⟨hy.1, Q.mem_U _⟩)).of_le
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hRe : ContDiffAt ℝ 2 (fun v => ((G ∘ (A.chart j).symm) v).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr hev, levi_add_smul 1 h2 hRe, levi_re_analytic hGa, mul_zero, add_zero, ← hφ]
  exact hP _ j y ⟨hy.1, P.mem_U _⟩ w

end PullTop

end GlobalTheory.CompanionTheory.Ar.Giv

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem pullbackStatement : PullbackStatement := by
  intro e e' X X' _ _ _ _ _ _ A A' h hh Θ L Θ' s n n' m W m' W' hΘ hΘp hΘ' hΘ'p hL hs hsnc hs0
    hsnc' th ph phT C₅ C t₀ hSW hF hC2
  obtain ⟨hth, hSm, hPshOn, hbd⟩ := hSW
  have hΘpsh : IsPsh A Θ := TailBoundAlt.isPsh_of_isPosPot A Θ hΘp
  have hΘ'psh : IsPsh A' Θ' := TailBoundAlt.isPsh_of_isPosPot A' Θ' hΘ'p
  have hΘpb : IsPotential A' (Θ.pullback h hh.1) := isPotentialPullback A A' h hh Θ hΘ
  obtain ⟨K, hK0, -, hKpsh⟩ := TailBoundAlt.exists_psh_chern_bound A' Θ' (Θ.pullback h hh.1) hΘ' hΘ'p hΘpb
  have ht₀ : 0 < t₀ := hF.1
  have hU : IsOpen (bdry s)ᶜ := (LeviFormBoundaryTopology.isClosed_bdry hs).isOpen_compl
  set M : ℝ := max 1 K with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMK : K ≤ M := le_max_right _ _
  set C' : ℝ := |C| * M with hC'
  set t₁ : ℝ := min t₀ (Real.exp (-Real.exp 1)) with ht₁
  have ht₁0 : 0 < t₁ := lt_min ht₀ (Real.exp_pos _)
  have ht₁t₀ : t₁ ≤ t₀ := min_le_left _ _
  have ht₁e : t₁ ≤ Real.exp (-Real.exp 1) := min_le_right _ _
  have hCC' : |C| ≤ C' := le_mul_of_one_le_right (abs_nonneg C) hM1
  have F1 := isRegFamily_mono A Θ L s th ph phT C t₀ |C| t₁ hΘ hΘpsh hth hs0 hF le_rfl ht₁0 ht₁t₀ ht₁e
  have F2 := isRegFamily_mono A Θ L s th ph phT C t₀ C' t₁ hΘ hΘpsh hth hs0 hF hCC' ht₁0 ht₁t₀ ht₁e
  refine ⟨C', t₁, ⟨isPotentialPullback A A' h hh th hth, ?_, ?_, fun y hy => hbd (h y) hy⟩, ?_, ?_⟩
  · have := smoothOn_pull hh hU hSm
    rwa [Set.preimage_compl] at this
  · have := isPshOn_pull hh hU hth hSm hPshOn
    rwa [Set.preimage_compl] at this
  · obtain ⟨-, -, F1⟩ := F1
    obtain ⟨h1, h2, F2⟩ := F2
    refine ⟨h1, h2, fun t ht htt => ?_⟩
    obtain ⟨a1, a2, a3, a4, -, a6, a7, a8⟩ := F2 t ht htt
    obtain ⟨b1, -, -, -, b5, -⟩ := F1 t ht htt
    have hsm : A'.Smooth (phT t ∘ h) := by
      have := smoothOn_pull hh isOpen_univ a1
      rwa [Set.preimage_univ] at this
    refine ⟨hsm, fun y => a2 (h y), fun y hy => a3 (h y) hy, fun y => a4 (h y), ?_,
      fun y hy hyr => a6 (h y) hy hyr, fun y hy => a7 (h y) hy,
      fun t' h1 h2 y => a8 t' h1 h2 (h y)⟩

    set ε : ℝ := epsT |C| t with hε
    have hq := loglog_quot_nonneg ht (htt.trans ht₁e)
    have hε0 : 0 ≤ ε := by
      rw [hε, epsT_eq_mul]; exact mul_nonneg (abs_nonneg C) hq
    have hε' : epsT C' t = M * ε := by
      rw [hε, epsT, epsT, hC']; ring
    have hεK : 0 ≤ M * ε - K * ε := by nlinarith
    have hP0 : IsPotential A (th + LocPot.ofFun (phT t) + Θ.rsmul ε) :=
      isPotentialAdd A _ _ (isPotentialAdd A _ _ hth (isPotential_ofFun A _ b1))
        (isPotentialRsmul A ε Θ hΘ)
    have hD : IsPotential A' (Θ'.rsmul K + (Θ.pullback h hh.1).rsmul (-1)) :=
      isPotentialAdd A' _ _ (isPotentialRsmul A' K Θ' hΘ') (isPotentialRsmul A' (-1) _ hΘpb)
    have hS1 := isPotentialPullback A A' h hh _ hP0
    have hS1p := isPsh_pull hh hP0 b5
    have hS2 := isPotentialRsmul A' ε _ hD
    have hS2p := isPshRsmul A' ε _ hε0 hD hKpsh
    have hS3 := isPotentialRsmul A' (M * ε - K * ε) Θ' hΘ'
    have hS3p := isPshRsmul A' (M * ε - K * ε) Θ' hεK hΘ' hΘ'psh
    have hS := isPshAdd A' _ _ (isPotentialAdd A' _ _ hS1 hS2) hS3
      (isPshAdd A' _ _ hS1 hS2 hS1p hS2p) hS3p
    have hT : IsPotential A' (th.pullback h hh.1 + LocPot.ofFun (phT t ∘ h) + Θ'.rsmul (epsT C' t)) :=
      isPotentialAdd A' _ _ (isPotentialAdd A' _ _ (isPotentialPullback A A' h hh th hth)
        (isPotential_ofFun A' _ hsm)) (isPotentialRsmul A' _ Θ' hΘ')
    refine isPsh_of_phi_eq hT ?_ hS
    funext x y
    show th.φ (h x) (h y) + phT t (h y) + ε * Θ.φ (h x) (h y) +
        ε * (K * Θ'.φ x y + -1 * Θ.φ (h x) (h y)) + (M * ε - K * ε) * Θ'.φ x y =
      th.φ (h x) (h y) + phT t (h y) + epsT C' t * Θ'.φ x y
    rw [hε']
    ring
  · have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), A.Smooth (phT t) :=
      Filter.mem_of_superset (Ioc_mem_nhdsGT ht₀) fun t ht => (hF.2.2 t ht.1 ht.2).1
    exact regular_family_C2_pullback_of_open A A' h hh s ph phT hU hSm hev hC2

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFirst
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_finTail {d : ℕ} (u : Fin (d + 1) → ℂ) :
    AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => (Fin.tail u : Fin d → ℂ)) u := by
  have h : (fun u : Fin (d + 1) → ℂ => (Fin.tail u : Fin d → ℂ)) =
      ⇑(ContinuousLinearMap.pi fun i : Fin d =>
        (ContinuousLinearMap.proj i.succ : (Fin (d + 1) → ℂ) →L[ℂ] ℂ)) := by
    funext u i
    rfl
  rw [h]
  exact ContinuousLinearMap.analyticAt _ _

theorem analyticAt_det_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : Type} [Fintype n]
    [DecidableEq n] (A : E → Matrix n n ℂ) (x : E) (h : ∀ r s, AnalyticAt ℂ (fun u => A u r s) x) :
    AnalyticAt ℂ (fun u => (A u).det) x := by
  simp only [Matrix.det_apply']
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => h _ _)

theorem analyticAt_minorIJ_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {N : ℕ}
    (A : E → Matrix (Fin N) (Fin N) ℂ) (x : E) (h : ∀ r s, AnalyticAt ℂ (fun u => A u r s) x)
    (I J : Finset (Fin N)) : AnalyticAt ℂ (fun u => minorIJ (A u) I J) x := by
  by_cases e : I.card = J.card
  · simp only [minorIJ, dif_pos e]
    exact analyticAt_det_of_entries _ x fun r s => h _ _
  · simp only [minorIJ, dif_neg e]
    exact analyticAt_const

theorem analyticAt_flagAt_entry {Ψ : Type} [DecidableEq Ψ] {N d : ℕ} (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (τ : Ψ) (ca cb : Fin N) (τ' : Ψ) (u₀ : Fin (d + 1) → ℂ)
    (hH : ∀ τ'' r s, AnalyticAt ℂ (fun w => H τ'' w r s) (Fin.tail u₀)) (r s : Fin N) :
    AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => flagAt H τ ca cb (u 0) (Fin.tail u) τ' r s) u₀ := by
  have hHt : ∀ τ'' r s, AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => H τ'' (Fin.tail u) r s) u₀ :=
    fun τ'' r s => (hH τ'' r s).comp (analyticAt_finTail u₀)
  have h0 : AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => u 0) u₀ :=
    (ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℂ) →L[ℂ] ℂ).analyticAt _
  unfold flagAt
  by_cases h : τ' = τ
  · simp only [if_pos h, Matrix.mul_apply, Matrix.add_apply]
    refine Finset.analyticAt_fun_sum _ fun t _ => (hHt _ _ _).mul (analyticAt_const.add ?_)
    by_cases e : cb = t ∧ ca = s
    · simpa only [Matrix.single_apply, if_pos e] using h0
    · simpa only [Matrix.single_apply, if_neg e] using analyticAt_const
  · simp only [if_neg h]
    exact hHt _ _ _

theorem sameOrbit_basePart {K : Type} {ι : K → Type} {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem coord_ne_zero_of_X_notMem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {z : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal z) : z q ≠ 0 := fun h0 => h (by
  show mConeMap z (X q) = 0
  rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem exists_normalised_exact {M : FlagModel y Ψ N j} (F : FrameData ι Ψ N M.Ω M.blk) (z₀ : (Σ k, ι k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (hne : ∀ k : NonPluckerBlocks M.blk, z₀ ⟨k.1, F.c k⟩ ≠ 0)
    (hex : ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) z₀ (h τ')) :
    ∃ z : (Σ k, ι k) → ℂ, SameOrbit z₀ z ∧ (∀ k, basePart M.blk z ⟨k, F.c k⟩ = 1) ∧
      ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) z (h τ') := by
  by_cases hp : Nonempty (Ψ × Fin N)
  · obtain ⟨⟨τ₀, i₀⟩⟩ := hp
    exact ⟨z₀, ⟨fun _ => 1, fun _ => one_ne_zero, by funext p; simp⟩, (hex τ₀ i₀).1, hex⟩
  · have hb : ∀ (k : K) p, M.blk p ≠ some k := fun k p => (hp ⟨p⟩).elim
    refine ⟨fun q => z₀ q / z₀ ⟨q.1, F.c ⟨q.1, hb q.1⟩⟩,
      ⟨fun k => z₀ ⟨k, F.c ⟨k, hb k⟩⟩, fun k => hne ⟨k, hb k⟩, ?_⟩, ?_, fun τ' i => (hp ⟨(τ', i)⟩).elim⟩
    · funext q
      rw [mul_div_cancel₀ _ (hne ⟨q.1, hb q.1⟩)]
    · rintro ⟨k, hk⟩
      exact div_self (hne ⟨k, hb k⟩)

theorem exact_points_holomorphic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a ca cb : Fin N) (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∃ zex : (Fin (d + 1) → ℂ) → (Σ k, ι k) → ℂ, (∀ q', AnalyticOnNhd ℂ (fun u => zex u q') {u : Fin (d + 1) → ℂ | Fin.tail u ∈ Un}) ∧ ∀ u : Fin (d + 1) → ℂ, Fin.tail u ∈ Un → zex u ∈ mcPts (mCoordIdeal y) ∧ ∀ x₀, FA.Re.π x₀ = ΦYn u → SameOrbit (FA.Re.R.lift x₀ x₀) (zex u) ∧ SameOrbit (basePart M.blk (zex u)) (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u))) ∧ ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ', i) (zex u) (flagAt H τ ca cb (u 0) (Fin.tail u) τ') := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a ca cb X q Un Gn ΦYn ΦWn l H bp hUn hD
  obtain ⟨hH, hbc, hba, hbp, -, hex, -⟩ := hD
  have hbij := realis_bijective_of_degree_one K ι (d + 1) _ FA.S _ FA.Re FA.deg_one FA.br_empty
  have hyh : IsMultiHomogIdeal (mCoordIdeal y) :=
    GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal y
  have key : ∀ u : Fin (d + 1) → ℂ, Fin.tail u ∈ Un → ∃ z : (Σ k, ι k) → ℂ,
      z ∈ mcPts (mCoordIdeal y) ∧ (∀ x₀, FA.Re.π x₀ = ΦYn u → SameOrbit (FA.Re.R.lift x₀ x₀) z) ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u))) ∧
      (∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ', i) z (flagAt H τ ca cb (u 0) (Fin.tail u) τ')) ∧
      ∀ k, basePart M.blk z ⟨k, (BM.F l).c k⟩ = 1 := by
    intro u hu
    obtain ⟨x₀, hx₀⟩ := hbij.2 (ΦYn u)
    obtain ⟨z₀, ho, hb, he⟩ := hex u hu x₀ hx₀
    have hgood := BM.good l _ (hbp _ hu).1.1
    have hne : ∀ k : NonPluckerBlocks M.blk, z₀ ⟨k.1, (BM.F l).c k⟩ ≠ 0 := by
      intro k
      obtain ⟨c, hc, hcz⟩ := hb
      have h1 := congrFun hcz ⟨k, (BM.F l).c k⟩
      have h2 : basePart M.blk z₀ ⟨k, (BM.F l).c k⟩ = z₀ ⟨k.1, (BM.F l).c k⟩ := rfl
      rw [← h2, h1]
      exact mul_ne_zero (hc k) (coord_ne_zero_of_X_notMem (hgood.1 k))
    obtain ⟨z, hz, hn, hz'⟩ := exists_normalised_exact (BM.F l) z₀ _ hne he
    refine ⟨z, ?_, ?_, ?_, hz', hn⟩
    · exact mem_mcPts_of_sameOrbit hyh (orbit_symm (orbit_trans ho hz))
        (FA.Re.R.mem x₀ x₀ (FA.Re.R.mem_U x₀))
    · intro x₁ hx₁
      obtain rfl := hbij.1 (hx₁.trans hx₀.symm)
      exact orbit_trans ho hz
    · exact orbit_trans (orbit_symm (sameOrbit_basePart M.blk hz)) hb
  choose! zex hz using key
  refine ⟨zex, ?_, fun u hu => ⟨(hz u hu).1, fun x₀ hx =>
    ⟨(hz u hu).2.1 x₀ hx, (hz u hu).2.2.1, (hz u hu).2.2.2.1⟩⟩⟩
  rintro ⟨k, m⟩ u₀ hu₀
  have hu₀' : (Fin.tail u₀ : Fin d → ℂ) ∈ Un := hu₀
  have htail : Tendsto (fun u : Fin (d + 1) → ℂ => (Fin.tail u : Fin d → ℂ)) (𝓝 u₀) (𝓝 (Fin.tail u₀)) :=
    (analyticAt_finTail u₀).continuousAt
  have hevU : ∀ᶠ u : Fin (d + 1) → ℂ in 𝓝 u₀, (Fin.tail u : Fin d → ℂ) ∈ Un := htail (hUn.mem_nhds hu₀')
  have hgood₀ := BM.good l _ (hbp _ hu₀').1.1
  by_cases hk : ∃ p, M.blk p = some k
  · obtain ⟨p, hp⟩ := hk
    have hval : ∀ s, RegAt M.x (mCoordIdeal (BM.Rb.lift (bp (Fin.tail u₀)) (bp (Fin.tail u₀)))) s →
        AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => valAt M.x s (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u)))) u₀ :=
      fun s hs => (analyticAt_valAt_lift_family (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x s d n BM.Rb Un bp (Fin.tail u₀)
        hUn hu₀' hbc hba hs).comp (analyticAt_finTail u₀)
    have hsum : AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => ∑ I,
        valAt M.x ((BM.F l).u ⟨k, m⟩ I) (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u))) *
          minorIJ (flagAt H τ ca cb (u 0) (Fin.tail u) p.1) I (stepCols N j p.2)) u₀ :=
      Finset.analyticAt_fun_sum _ fun I _ => (hval _ ((hgood₀.2.1 _ I).1)).mul
        (analyticAt_minorIJ_of_entries _ _ (analyticAt_flagAt_entry H τ ca cb p.1 u₀
          (fun τ'' r s => hH τ'' r s _ hu₀')) _ _)
    refine hsum.congr ?_
    filter_upwards [hevU] with u hu
    obtain ⟨-, -, hb, he, -⟩ := hz u hu
    rw [(he p.1 p.2).2 k hp m]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [valAt_eq_of_sameOrbit (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x _ _ _ (BM.Rb.mem _ _ (BM.Rb.mem_U _))
      (orbit_symm hb)]
  · have hkb : ∀ p, M.blk p ≠ some k := fun p hp => hk ⟨p, hp⟩
    set kb : NonPluckerBlocks M.blk := ⟨k, hkb⟩ with hkb'
    set b₀ := bp (Fin.tail u₀) with hb₀
    have hlift : ∀ q : Σ k, baseIdx ι M.blk k,
        AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => BM.Rb.lift b₀ (bp (Fin.tail u)) q) u₀ :=
      fun q => (analyticAt_comp_of_holo_in_charts d n BM.Rb.X BM.Rb.A Un bp (Fin.tail u₀) (BM.Rb.U b₀)
        (fun x => BM.Rb.lift b₀ x q) hUn hu₀' hbc hba (BM.Rb.isOpen_U _) (BM.Rb.mem_U _)
        (BM.Rb.holo b₀ q)).comp (analyticAt_finTail u₀)
    have hden : BM.Rb.lift b₀ (bp (Fin.tail u₀)) ⟨kb, (BM.F l).c kb⟩ ≠ 0 :=
      coord_ne_zero_of_X_notMem (hgood₀.1 kb)
    refine ((hlift ⟨kb, m⟩).div (hlift ⟨kb, (BM.F l).c kb⟩) hden).congr ?_
    have hca : ContinuousAt bp (Fin.tail u₀) := hbc.continuousAt (hUn.mem_nhds hu₀')
    filter_upwards [hevU, htail (hca ((BM.Rb.isOpen_U b₀).mem_nhds (BM.Rb.mem_U b₀)))] with u hu hbu
    obtain ⟨-, -, hb, -, hn⟩ := hz u hu
    obtain ⟨c, hc, hcz⟩ := orbit_trans hb (BM.Rb.compat (bp (Fin.tail u)) b₀ (bp (Fin.tail u)) ⟨BM.Rb.mem_U _, hbu⟩)
    have h1 : c kb * BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, (BM.F l).c kb⟩ = 1 := by
      rw [← hn kb, hcz]
    have h2 : zex u ⟨k, m⟩ = c kb * BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, m⟩ := congrFun hcz ⟨kb, m⟩
    have h3 : BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, (BM.F l).c kb⟩ ≠ 0 := right_ne_zero_of_mul_eq_one h1
    show BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, m⟩ / BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, (BM.F l).c kb⟩ = zex u ⟨k, m⟩
    rw [h2, div_eq_iff h3]
    linear_combination (-(BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, m⟩)) * h1

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartThird
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.GramPlane

theorem contDiffOn_conj_mul_mul {e N : ℕ} {Un : Set (Fin e → ℂ)} (hUn : IsOpen Un) (A G : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ r s, AnalyticOnNhd ℂ (fun w => A w r s) Un)
    (hG : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => G w r s) Un) (r s : Fin N) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => ((A w)ᴴ * G w * A w) r s) Un := by
  have hA' : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => A w r s) Un := fun r s =>
    ((hA r s).contDiffOn hUn.uniqueDiffOn).restrict_scalars ℝ
  have hAc : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => star (A w r s)) Un := fun r s => by
    first
      | exact ContDiffOn.star (hA' r s)
      | exact (Complex.conjCLE.contDiff.comp_contDiffOn (hA' r s))
      | (have h := Complex.conjCLE.contDiff.comp_contDiffOn (hA' r s)
         simpa [Function.comp_def] using h)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine ContDiffOn.sum fun k _ => ?_
  refine ContDiffOn.mul ?_ (hA' k s)
  refine ContDiffOn.sum fun i _ => ?_
  exact (hAc i r).mul (hG i k)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.GramPlane

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem contDiffOn_gram_plane : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => Gn w r s) Un := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb _ _ _ _ X q Un Gn ΦYn ΦWn l H bp hUn hF r s
  obtain ⟨hH, hbp, hch, hO, hGn, -, -⟩ := hF
  have hGs : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => BM.G l τ (bp w) r s) Un :=
    _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_gram_comp_basePoint K ι Φ y Ψ N j M n d BM l τ Un bp hUn hbp hch (fun w hw => (hO w hw).1)
  have hMs : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) r s) Un :=
    GramPlane.contDiffOn_conj_mul_mul hUn (H τ) (fun w => BM.G l τ (bp w)) (hH τ) hGs
  have hnum := MinorSmooth.contDiffOn_minorIJ N d Un (fun w => (H τ w)ᴴ * BM.G l τ (bp w) * H τ w)
    (insert (![ca, cb] r) ((stepCols N j a).erase ca)) (insert (![ca, cb] s) ((stepCols N j a).erase ca)) hMs
  have hden := MinorSmooth.contDiffOn_minorIJ N d Un (fun w => (H τ w)ᴴ * BM.G l τ (bp w) * H τ w)
    ((stepCols N j a).erase ca) ((stepCols N j a).erase ca) hMs
  have hne : ∀ w ∈ Un, minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w)
      ((stepCols N j a).erase ca) ((stepCols N j a).erase ca) ≠ 0 := by
    intro w hw
    have hGp := (BM.G_pos l τ (bp w) (hO w hw).1).2
    have hdet := ((hO w hw).2 τ).2
    have hinj : Function.Injective (H τ w).mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr hdet
    exact (SchurCalc.minor_pos (hGp.conjTranspose_mul_mul_same hinj) _).ne'
  have hq := hnum.mul (hden.inv hne)
  refine hq.congr fun w hw => ?_
  have e := hGn w hw r s
  clear * - e
  simp only [e, div_eq_mul_inv, Pi.inv_apply]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightThresholdLimitCoefficients
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem tower_seq : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem) (B : ℕ) (u : Wt Ψ N) (g : ℝ) (c : T.Comp) (s : ℕ → ℝ) (q : ℕ → ℕ) (m : ℕ → Option (Ψ × Fin N) → ℤ), IsFullIntersectionSystem II → T.T1 II → WeightHyp T.j u g → bigB0 u g < B + 1 → (∀ n, 0 < s n) → Tendsto s atTop (𝓝 0) → (∀ n, 0 < q n) → (∀ n j, (m n j : ℝ) = q n * (T.M B c).coef (T.lamS u (s n)) (s n) j) → (∀ᶠ n in atTop, IsNefH (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n))) ∧ Tendsto (fun n => geomDeg (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) / (q n : ℝ) ^ dimFl Ψ N) atTop (𝓝 ((T.M B c).δ * (T.vol c * flagDeg u))) ∧ Tendsto (fun n => normHt II (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) / q n) atTop (𝓝 (T.slope II B c u)) ∧ 0 < T.vol c * flagDeg u := by
  intro Ψ _ _ N T II B u g c s q m hII hT1 hW hB hs hs0 hq hm
  obtain ⟨h1, -, h3, h4, h5⟩ := hT1 u g hW B hB c
  have hs' : Tendsto s atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hs0, Eventually.of_forall fun n => hs n⟩
  have hδ : ((T.M B c).δ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (T.M B c).δ_pos.ne'
  have hqn : ∀ n, (q n : ℝ) ≠ 0 := fun n => Nat.cast_ne_zero.2 (hq n).ne'
  have hgeo : ∀ n, geomDeg (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) =
      (T.M B c).δ * (q n : ℝ) ^ dimFl Ψ N * T.mDeg B c u (s n) := by
    intro n
    have := geoFun_comb_mixed II hII Ψ N (T.M B c) (scale (s n)) (fun _ => T.lamS u (s n)) (fun _ => s n) (q n)
      (fun _ => m n) (fun _ j => hm n j)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact this
  have har : ∀ n, II (T.M B c).K (T.M B c).ι (T.M B c).P (dimFl Ψ N + 1)
      (fun _ => combLine ((T.M B c).line (scale (s n))) (m n)) =
      (T.M B c).δ * (q n : ℝ) ^ (dimFl Ψ N + 1) * T.mbarTop II B c u (s n) := fun n =>
    top_comb_eq_arFun II hII Ψ N (T.M B c) (scale (s n)) (T.lamS u (s n)) (s n) (q n) (m n) (hm n)
  refine ⟨?_, ?_, ?_, h4⟩
  · filter_upwards [hs'.eventually h1] with n hn
    have a := (nefFib_integral_multiple Ψ N (T.M B c) (scale (s n)) (T.lamS u (s n)) (s n) (q n) (m n) (hm n)).2 hn.1
    have b := RootFieldNumerics.root_model_line_semipositive Ψ N (T.M B c) (scale (s n)) (T.lamS u (s n)) (s n) (q n) (m n) (hm n) hn.2
    exact ⟨⟨_, le_rfl, b.1⟩, b.2, a⟩
  · refine ((h3.comp hs').const_mul ((T.M B c).δ : ℝ)).congr fun n => ?_
    rw [hgeo n]
    have := hqn n
    simp only [Function.comp]
    field_simp
  · refine (h5.comp hs').congr fun n => ?_
    unfold normHt
    rw [hgeo n, har n]
    have := hqn n
    simp only [Function.comp]
    by_cases h0 : T.mDeg B c u (s n) = 0
    · simp [h0]
    · have h2 : ((dimFl Ψ N : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring

end GlobalTheory.CompanionTheory.Ar.Small
end

