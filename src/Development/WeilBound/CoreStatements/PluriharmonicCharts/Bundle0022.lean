module

public import Mathlib
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0121
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0110
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0111
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0120
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0116
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0062
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0123
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0055
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0020
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0050

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.AnalyticAtFlagPt
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace PositivityTheory.Xgp.c_unif

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {n : ℕ}

theorem analyticAt_flagPt {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : FrameData ι Ψ N M.Ω M.blk)
    {b : E → (Σ k, baseIdx ι M.blk k) → ℂ} {h : Ψ → E → Matrix (Fin N) (Fin N) ℂ} {w : E}
    (hb : ∀ q, AnalyticAt ℂ (fun u => b u q) w) (hv : ∀ q I, AnalyticAt ℂ (fun u => valAt M.x (F.u q I) (b u)) w)
    (hh : ∀ τ r s, AnalyticAt ℂ (fun u => h τ u r s) w) (q : Σ k, ι k) :
    AnalyticAt ℂ (fun u => FC.flagPt M F (b u) (fun τ => h τ u) q) w := by
  by_cases hk : ∀ p, M.blk p ≠ some q.1
  · simp only [FC.flagPt, dif_pos hk]
    exact hb _
  · simp only [FC.flagPt, dif_neg hk]
    exact Finset.analyticAt_fun_sum _ fun I _ => (hv q I).mul
      (Fib.analyticAt_minorIJ_of_entries _ w (hh _) _ _)

variable (BM : BaseMetric M n) {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {pr : X → BM.Rb.X}

theorem bvec_holo (hp : HoloMap A BM.Rb.A pr) {W : Set X} (hW : IsOpen W) {l : Fin BM.q}
    (hl : ∀ x ∈ W, pr x ∈ BM.O l) :
    (∀ q, A.HoloOn W fun x => FC.bvec BM l (pr x) q) ∧
      ∀ s : M.Ω, (∀ b ∈ BM.O l, RegAt M.x (mCoordIdeal (FC.bvec BM l b)) s) →
        A.HoloOn W fun x => valAt M.x s (FC.bvec BM l (pr x)) := by
  have key := fun k => _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_val_analytic K ι Φ y Ψ N j M n BM l e ((A.chart k).target ∩ (A.chart k).symm ⁻¹' W)
    (pr ∘ (A.chart k).symm) ((A.chart k).isOpen_inter_preimage_symm hW)
    (hp.1.comp_continuousOn ((A.chart k).continuousOn_symm.mono Set.inter_subset_left))
    (fun m => (hp.2 k m).mono fun t ht => ⟨ht.1.1, ht.2⟩) (fun u hu => hl _ hu.2)
  exact ⟨fun q k => (key k).1 q, fun s hs k => (key k).2 s hs⟩

theorem step_of_orbit {F : FrameData ι Ψ N M.Ω M.blk} {b : (Σ k, baseIdx ι M.blk k) → ℂ} {z : (Σ k, ι k) → ℂ}
    {h : Ψ → Matrix (Fin N) (Fin N) ℂ} (ho : SameOrbit z (FC.flagPt M F b h)) (p : Ψ × Fin N) (k : K)
    (hk : M.blk p = some k) : ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k,
      z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) b * minorIJ (h p.1) I (stepCols N j p.2) := by
  obtain ⟨c, hc, rfl⟩ := ho
  exact ⟨c k, hc k, fun m => by rw [← FC.flagPt_step M F b h hk m]⟩

theorem lowMat_props (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : IsBlockDiag j (lowMat c τ) ∧ IsLowerUni (lowMat c τ) :=
  ⟨fun a b h => (dif_neg fun e => h e.2).trans (if_neg fun e => h (by rw [e])),
    fun _ => (dif_neg fun e => lt_irrefl _ e.1).trans (if_pos rfl),
    fun _ _ h => (dif_neg fun e => lt_asymm h e.1).trans (if_neg h.ne)⟩

theorem lowMat_eq {c : LowIdx Ψ N j → ℂ} {τ : Ψ} {L : Matrix (Fin N) (Fin N) ℂ} (hb : IsBlockDiag j L)
    (hL : IsLowerUni L) (h : ∀ (a b : Fin N) (e : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)), c ⟨(τ, a, b), e⟩ = L a b) :
    lowMat c τ = L := by
  ext a b
  unfold lowMat
  split_ifs with h1 h2
  · exact h a b h1
  · rw [h2, hL.1]
  · rcases lt_or_gt_of_ne h2 with e | e
    · exact (hL.2 a b e).symm
    · exact (hb a b fun e' => h1 ⟨e, e'⟩).symm

theorem exists_holo_flags (hp : HoloMap A BM.Rb.A pr) {W : Set X} (hW : IsOpen W) {z : X → (Σ k, ι k) → ℂ}
    (hz : ∀ q, A.HoloOn W fun x => z x q) (hm : ∀ x ∈ W, z x ∈ mcPts (mCoordIdeal y))
    (hb : ∀ x ∈ W, SameOrbit (basePart M.blk (z x)) (BM.Rb.lift (pr x) (pr x))) {l : Fin BM.q}
    (hl : ∀ x ∈ W, pr x ∈ BM.O l) {x₀ : X} (hx₀ : x₀ ∈ W) :
    ∃ W' : Set X, IsOpen W' ∧ x₀ ∈ W' ∧ W' ⊆ W ∧ ∃ (h₀ : Ψ → Matrix (Fin N) (Fin N) ℂ)
      (L : Ψ → X → Matrix (Fin N) (Fin N) ℂ), (∀ τ, IsBlockDiag j (h₀ τ) ∧ (h₀ τ).det ≠ 0) ∧
      (∀ τ a b, A.HoloOn W' fun x => L τ x a b) ∧ (∀ τ x, IsBlockDiag j (L τ x) ∧ IsLowerUni (L τ x)) ∧
      ∀ x ∈ W', SameOrbit (z x) (FC.flagPt M (BM.F l) (FC.bvec BM l (pr x)) fun τ => h₀ τ * L τ x) := by
  have hj := M.j_le
  have hF := BM.isFrame l
  have hg := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good K ι Φ y Ψ N j M n BM l
  have hex := fun x (hx : x ∈ W) => _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_flagPt_of_orbit K ι Φ y Ψ N j M n BM l (pr x) (hl x hx) (z x) (hm x hx) (hb x hx)
  obtain ⟨h₀, hh₀, ho₀⟩ := hex x₀ hx₀
  let tw : Fin N → K → Ψ → Finset (Fin N) → X → ℂ := fun i k τ J x =>
    twMinor M (BM.F l) (FC.bvec BM l (pr x)) i k (h₀ τ)⁻¹ (z x) J
  have htw : ∀ i k τ J, A.HoloOn W (tw i k τ J) := by
    intro i k τ J m t ht
    have hv := fun I (q : Σ k, ι k) => (bvec_holo BM hp hW hl).2 ((BM.F l).u' I q)
      (fun b hb => ((hg b hb).2.1.2.1 q I).2) m t ht
    show AnalyticAt ℂ (fun w => tw i k τ J ((A.chart m).symm w)) t
    simp only [tw, twMinor, pluck]
    exact Finset.analyticAt_fun_sum _ fun I _ => analyticAt_const.mul
      (Finset.analyticAt_fun_sum _ fun r _ => (hv I ⟨k, r⟩).mul (hz ⟨k, r⟩ m t ht))
  let T := {pk : (Ψ × Fin N) × K // M.blk pk.1 = some pk.2}
  let den : T → X → ℂ := fun t => tw t.1.1.2 t.1.2 t.1.1.1 (stepCols N j t.1.1.2)
  have tweq : ∀ x ∈ W, ∀ h' : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ, IsBlockDiag j (h' τ)) →
      SameOrbit (z x) (FC.flagPt M (BM.F l) (FC.bvec BM l (pr x)) h') → ∀ t : T, ∃ α : ℂ, α ≠ 0 ∧
        den t x = α * minorIJ ((h₀ t.1.1.1)⁻¹ * h' t.1.1.1) (stepCols N j t.1.1.2) (stepCols N j t.1.1.2) := by
    intro x hx h' hb' ho t
    obtain ⟨α, hα, hzk⟩ := step_of_orbit ho t.1.1 t.1.2 t.2
    exact ⟨α, hα, _root_.GlobalTheory.CompanionTheory.Ar.PB.WMan.TwRead.main K ι Φ y Ψ N j M (BM.F l) _ t.1.1 t.1.2 _ _ _ α _ hF (hg _ (hl x hx)).1
      (hg _ (hl x hx)).2.1 t.2 (hb' _) hzk⟩
  refine ⟨{x | x ∈ W ∧ ∀ t, den t x ≠ 0}, isOpen_ne hW fun t => htw _ _ _ _, ⟨hx₀, fun t => ?_⟩, fun x hx => hx.1, h₀,
    fun τ x => lowMat (fun q : LowIdx Ψ N j =>
      lowRead M (BM.F l) (FC.bvec BM l (pr x)) h₀ (z x) q.1.1 q.1.2.1 q.1.2.2) τ, hh₀, fun τ a b => ?_,
    fun τ x => lowMat_props _ _, fun x hx => ?_⟩
  · obtain ⟨α, hα, e⟩ := tweq x₀ hx₀ h₀ (fun τ => (hh₀ τ).1) ho₀ t
    rw [e, Matrix.nonsing_inv_mul _ (hh₀ _).2.isUnit, CPts.minorIJ_one, mul_one]
    exact hα
  · by_cases h1 : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · simp only [lowMat, dif_pos h1, lowRead]
      rcases hk : M.blk (τ, stepOf N j b) with _ | k
      · exact fun _ => analyticOnNhd_const
      · intro m t ht
        exact AnalyticAt.div (htw (stepOf N j b) k τ _ m t ⟨ht.1, ht.2.1⟩) (htw (stepOf N j b) k τ _ m t ⟨ht.1, ht.2.1⟩)
          (ht.2.2 ⟨((τ, stepOf N j b), k), hk⟩)
    · simp only [lowMat, dif_neg h1]
      exact fun _ => analyticOnNhd_const
  · obtain ⟨h', hh', ho⟩ := hex x hx.1
    have hLU : ∀ τ, ∃ L U : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j L ∧ IsLowerUni L ∧ IsBlockDiag j U ∧
        U.BlockTriangular id ∧ (∀ c, U c c ≠ 0) ∧ (h₀ τ)⁻¹ * h' τ = L * U := by
      intro τ
      refine _root_.GlobalTheory.CompanionTheory.Ar.PB.WMan.LU.exists_lower_upper N j _ hj (((hh₀ τ).1.inv (hh₀ τ).2.isUnit).mul (hh' τ).1) ?_ fun i hi => ?_
      · rw [Matrix.det_mul]
        exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (hh₀ τ).2.isUnit).ne_zero (hh' τ).2
      · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 fun e => (M.blk_none (τ, i)).1 e hi
        obtain ⟨α, -, e⟩ := tweq x hx.1 h' (fun τ => (hh' τ).1) ho ⟨((τ, i), k), hk⟩
        have := hx.2 ⟨((τ, i), k), hk⟩
        rw [e] at this
        exact right_ne_zero_of_mul this
    choose L U hLb hLu hUb hUt hUd hLU using hLU
    have e1 : ∀ τ, lowMat (fun q : LowIdx Ψ N j =>
        lowRead M (BM.F l) (FC.bvec BM l (pr x)) h₀ (z x) q.1.1 q.1.2.1 q.1.2.2) τ = L τ := fun τ =>
      lowMat_eq (hLb τ) (hLu τ) fun a b e => LowRead.main K ι Φ y Ψ N j M (BM.F l) _ h₀ τ a b (z x) (h' τ) (L τ) (U τ)
        hF (hg _ (hl x hx.1)).1 (hg _ (hl x hx.1)).2.1 (hh' τ).1 (hLU τ) (hLb τ) (hLu τ) (hUb τ) (hUt τ)
        (fun c _ => hUd τ c) e.1 e.2 fun k hk => step_of_orbit ho (τ, stepOf N j b) k hk
    simp only [e1]
    have e2 : h' = fun τ => (h₀ τ * L τ) * U τ := funext fun τ => by
      rw [Matrix.mul_assoc, ← hLU, Matrix.mul_nonsing_inv_cancel_left _ _ (hh₀ τ).2.isUnit]
    refine orbit_trans ho ?_
    rw [e2]
    refine _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.sameOrbit_flagPt_mul K ι Φ y Ψ N j M _ _ (fun τ => h₀ τ * L τ) U fun τ => ⟨hUb τ, hUt τ, ?_⟩
    rw [Matrix.det_of_upperTriangular (hUt τ)]
    exact Finset.prod_ne_zero_iff.2 fun c _ => hUd τ c

end PositivityTheory.Xgp.c_unif
end
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.ContinuousOnLogNormSec
section
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB

namespace PositivityTheory.Xgp.sq_limit

open GlobalTheory.CompanionTheory.Ar.Giv GlobalTheory.CompanionTheory.Ar.Giv.SignedConv ReciprocityTheory.AnForm.M.FinHolAtlas

theorem continuousOn_logNormSec {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (L : LocPot X) (v : X → X → ℂ) (hL : IsPotential A L) (hv : IsSection A L v) :
    ContinuousOn (logNormSec L v) (bdry v)ᶜ := by
  intro y hy
  refine ContinuousAt.continuousWithinAt ?_
  have hy' : v y y ≠ 0 := hy
  have h1 : ContinuousAt (v y) y := LeviFormBoundaryTopology.continuousAt_of_holoOn A (hv.1 y) (L.mem_U y)
  have h2 : ContinuousAt (L.φ y) y :=
    LeviFormBoundaryTopology.continuousAt_of_smoothOn A (L.isOpen_U y) (hL.1 y) (L.mem_U y)
  have h3 : ContinuousAt (fun z => Real.log (‖v y z‖ * Real.exp (-L.φ y z))) y := by
    refine ContinuousAt.log (h1.norm.mul (Real.continuous_exp.continuousAt.comp h2.neg)) ?_
    exact mul_ne_zero (norm_ne_zero_iff.2 hy') (Real.exp_pos _).ne'
  refine h3.congr ?_
  filter_upwards [(L.isOpen_U y).mem_nhds (L.mem_U y)] with z hz
  unfold logNormSec
  rw [hv.2 y z z ⟨hz, L.mem_U z⟩]

theorem smoothOn_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {U V : Set X} {f : X → ℝ} (hUV : U ⊆ V) (h : A.SmoothOn V f) : A.SmoothOn U f :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hUV))

theorem isPshOn_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {U V : Set X} {P : LocPot X} (hUV : U ⊆ V) (h : IsPshOn A V P) : IsPshOn A U P :=
  fun x j y hy w => h x j y ⟨hy.1, hy.2.1, hUV hy.2.2⟩ w

theorem unifIntSigned (hU : UnifIntStatement) {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X) (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ)
    (hL : IsPotential A L) (hS : IsSection A L s) (hSNC : IsSNC A L s m W)
    (hs : ∀ y, logNormSec L s y ≤ 0) (L' : LocPot X) (v : X → X → ℂ) (Dg : Set X)
    (hL' : IsPotential A L') (hv : IsSection A L' v) (hvS : IsSNC A L' v ![1] ![Dg])
    (hsv : IsSNC A (L + L') (fun x y => s x y * v x y) (Fin.snoc m 1) (Fin.snoc W Dg))
    (hvn : ∀ y, logNormSec L' v y ≤ 0)
    (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ)
    (hSW : ∀ i, IsSingWeight A L s (th i) (ph i) C₅)
    (hRF : ∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀)
    (hC2 : ∀ i, IsRegFamilyC2 A s (ph i) (phT i)) :
    MIntegrable A (fun i => th i + LocPot.ofFun (ph i)) (logNormSec L' v) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable A (fun i => th i + LocPot.ofFun (phT i t)) (logNormSec L' v)) ∧
      Tendsto (fun t => mInt A (fun i => th i + LocPot.ofFun (phT i t)) (logNormSec L' v)) (𝓝[>] 0)
        (𝓝 (mInt A (fun i => th i + LocPot.ofFun (ph i)) (logNormSec L' v))) := by
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  set g := logNormSec L' v with hg
  have hΘpsh : IsPsh A Θ := isPsh_of_isPosPot A Θ hΘp
  set U : Set X := (bdry s)ᶜ ∩ (bdry v)ᶜ with hUdef
  have hUo : IsOpen U := (LeviFormBoundaryTopology.isClosed_bdry hS).isOpen_compl.inter
    (LeviFormBoundaryTopology.isClosed_bdry hv).isOpen_compl
  have hUs : U ⊆ (bdry s)ᶜ := Set.inter_subset_left
  have hnull : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0 := by
    intro j
    rw [hUdef, Set.compl_inter, Set.preimage_union, Set.inter_union_distrib_left]
    exact measure_union_null (chart_null A L s m W hS hSNC j) (chart_null A L' v _ _ hv hvS j)
  have hgc : ContinuousOn g U := (continuousOn_logNormSec A L' v hL' hv).mono Set.inter_subset_right
  have hmem : ∀ T : Finset (Fin e),
      (∀ i, IsSingWeight A L s (if i ∈ T then th i else LocPot.ofFun 0)
        (if i ∈ T then ph i else 0) |C₅|) ∧
      (∀ i, IsRegFamily A Θ L s (if i ∈ T then th i else LocPot.ofFun 0)
        (if i ∈ T then ph i else 0) (fun t => if i ∈ T then phT i t else 0) |C|
        (min t₀ (Real.exp (-Real.exp 1)))) ∧
      (∀ i, IsRegFamilyC2 A s (if i ∈ T then ph i else 0) (fun t => if i ∈ T then phT i t else 0)) := by
    intro T
    have hz : ∀ i : Fin e, IsSingWeight A L s (LocPot.ofFun 0) 0 |C₅| ∧
        IsRegFamily A Θ L s (LocPot.ofFun 0) 0 (fun _ => 0) |C| (min t₀ (Real.exp (-Real.exp 1))) ∧
        IsRegFamilyC2 A s 0 (fun _ => 0) := fun i =>
      zero_member A Θ L s |C₅| |C| _ hΘ hΘp hs (abs_nonneg _) (abs_nonneg _)
        (lt_min (hRF i).1 (Real.exp_pos _)) (min_le_right _ _)
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;> by_cases hi : i ∈ T <;>
      simp only [hi, ↓reduceIte]
    · exact isSingWeight_abs A L s _ _ _ hs (hSW i)
    · exact (hz i).1
    · exact isRegFamily_mono A Θ L s (th i) (ph i) (phT i) C t₀ |C| _ hΘ hΘpsh (hSW i).1 hs (hRF i)
        le_rfl (lt_min (hRF i).1 (Real.exp_pos _)) (min_le_left _ _) (min_le_right _ _)
    · exact (hz i).2.1
    · exact hC2 i
    · exact (hz i).2.2
  have hconv : ∀ T : Finset (Fin e),
      Integrable g (maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then ph i else 0) + Θ)) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), Integrable g (maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ))) ∧
      Tendsto (fun t => ∫ y, g y ∂maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) (𝓝[>] 0)
        (𝓝 (∫ y, g y ∂maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then ph i else 0) + Θ))) := by
    intro T
    obtain ⟨h1, h2, h3⟩ := hU A Θ L s m W hΘ hΘp hL hS hSNC hs L' v Dg hL' hv hvS hsv hvn
      (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then ph i else 0)
      (fun i t => if i ∈ T then phT i t else 0) |C₅| |C| _ (hmem T).1 (hmem T).2.1 (hmem T).2.2
    refine ⟨integrable_neg_iff.1 h1, h2.mono fun t ht => integrable_neg_iff.1 ht, ?_⟩
    simp only [integral_neg] at h3
    simpa only [neg_neg] using h3.neg
  have hlimT := fun T : Finset (Fin e) => _root_.GlobalTheory.CompanionTheory.Ar.Giv.mInt_eq_integral_maMeasure_off_null A U
    (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then ph i else 0) Θ hUo hnull
    (fun i => ((hmem T).1 i).1) hΘ hΘpsh (fun i => smoothOn_mono A hUs ((hmem T).1 i).2.1)
    (fun i => isPshOn_add_psh A _ _ _ Θ hUo ((hmem T).1 i).1 hΘ (smoothOn_mono A hUs ((hmem T).1 i).2.1)
      (isPshOn_mono A hUs ((hmem T).1 i).2.2.1) hΘpsh) g hgc (hconv T).1
  have hexpL := expand_mInt A U th ph Θ g hUo hnull (fun i => (hSW i).1) hΘ
    (fun i => smoothOn_mono A hUs (hSW i).2.1) (fun T => (hlimT T).1)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ i, A.Smooth (phT i t)) ∧
      ∀ T : Finset (Fin e), (∀ i, A.Smooth (if i ∈ T then phT i t else 0) ∧
        IsPsh A ((if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) ∧
        Integrable g (maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) := by
    refine (eventually_all.2 fun i => ?_).and (eventually_all.2 fun T => ?_)
    · exact (eventually_isPsh A Θ L s (th i) (ph i) (phT i) C t₀ hΘ hΘp (hSW i).1 (hRF i)).mono
        fun t ht => ht.1
    · refine (eventually_all.2 fun i => ?_).and (hconv T).2.1
      exact eventually_isPsh A Θ L s _ _ _ _ _ hΘ hΘp ((hmem T).1 i).1 ((hmem T).2.1 i)
  have hreg : ∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable A (fun i => th i + LocPot.ofFun (phT i t)) g ∧
      ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
        ∫ y, g y ∂maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ) =
        mInt A (fun i => th i + LocPot.ofFun (phT i t)) g := by
    filter_upwards [hev] with t ht
    have hmt := fun T : Finset (Fin e) => _root_.GlobalTheory.CompanionTheory.Ar.Giv.mInt_eq_integral_maMeasure_off_null A U
      (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then phT i t else 0) Θ hUo hnull
      (fun i => ((hmem T).1 i).1) hΘ hΘpsh (fun i => smoothOn_of_smooth A _ _ ((ht.2 T).1 i).1)
      (fun i => isPshOn_of_isPsh A _ _ ((ht.2 T).1 i).2) g hgc (ht.2 T).2
    have hx := expand_mInt A U th (fun i => phT i t) Θ g hUo hnull (fun i => (hSW i).1) hΘ
      (fun i => smoothOn_of_smooth A _ _ (ht.1 i)) (fun T => (hmt T).1)
    refine ⟨hx.1, ?_⟩
    rw [hx.2]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [(hmt T).2]
  refine ⟨hexpL.1, hreg.mono fun t ht => ht.1, ?_⟩
  rw [hexpL.2]
  refine Tendsto.congr' (hreg.mono fun t ht => ht.2) ?_
  refine tendsto_finsetSum _ fun T _ => ?_
  rw [(hlimT T).2]
  exact ((hconv T).2.2).const_mul _

theorem singular_part (hI : Inputs) {d : ℕ} {σ : Type} [Fintype σ] {SY : AnSys (d + 1) σ} {a₀ : σ}
    {ε : σ → ℤ} (Q : AnSq SY a₀ ε) (w : Fin (d + 2) → Option σ) :
    MIntegrable Q.SW.A (fun r => Q.SW.potH (w r)) (logNormSec Q.L' Q.v) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable Q.SW.A (fun r => Q.SW.potT (w r) t) (logNormSec Q.L' Q.v)) ∧
      Tendsto (fun t => mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (logNormSec Q.L' Q.v)) (𝓝[>] 0)
        (𝓝 (mInt Q.SW.A (fun r => Q.SW.potH (w r)) (logNormSec Q.L' Q.v))) :=
  unifIntSigned hI.unifInt Q.SW.A Q.SW.Θ Q.SW.L Q.SW.s Q.SW.m Q.SW.W Q.SW.potΘ Q.SW.posΘ Q.SW.potL
    Q.SW.sec Q.SW.snc Q.SW.norm_le Q.L' Q.v Q.Dg Q.potL' Q.secv Q.sncv Q.sncsv Q.normv
    (fun r => Q.SW.th (w r)) (fun r => Q.SW.ph (w r)) (fun r => Q.SW.phT (w r)) Q.SW.C₅ Q.SW.C Q.SW.t₀
    (fun r => Q.SW.sing (w r)) (fun r => Q.SW.reg (w r)) (fun r => Q.SW.c2 (w r))

end PositivityTheory.Xgp.sq_limit
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsFlagsLieCompactDominated
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace PositivityTheory.Xgp.FlagsLieBaseChange

theorem bc {S : Scheme.{0}} {G : Over S} [GrpObj G] (hs : Smooth G.hom) {R R' : Type} [Field R] [Field R']
    (f : R →+* R') (x : Spec (CommRingCat.of R) ⟶ S) (y : Spec (CommRingCat.of R') ⟶ S)
    (hy : Spec.map (CommRingCat.ofHom f) ≫ x = y) {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E']
    [Module R' E'] (M : LieModel G x E) (M' : LieModel G y E') :
    ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap f)) ≫ (M.pt e).left) ∧
      IsExtOver f j ∧ Submodule.span R' (Set.range j) = ⊤ ∧ Module.Finite R E := by
  subst hy
  let _ := f.toAlgebra
  obtain ⟨j, hj, hl, hb⟩ := PositivityTheory.HtPt.Htat.lie_bc S G R R' x E E' M M'
  haveI := hs
  haveI : Module.Finite R E := (PositivityTheory.HtPt.Htat.lie_fin S G R x E M).1
  let b₁ := Module.finBasis R E
  refine ⟨j, hj, ⟨hl, fun n b h => LiePull.indep_of_bases b₁ j (fun m B => (hb hs m B).1) b h⟩, ?_, inferInstance⟩
  refine top_le_iff.1 ((hb hs _ b₁).2.symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  exact ⟨_, rfl⟩

theorem basis {F Ω V W : Type} [Field F] [Field Ω] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module Ω W]
    [Module.Finite F V] {i : F →+* Ω} {j : V →+ W} (hj : IsExtOver i j) (U : Submodule F V) (U' : Submodule Ω W)
    (h : U' = Submodule.span Ω (j '' (U : Set V))) {n : ℕ} (B : Module.Basis (Fin n) Ω U') :
    ∃ b : Fin n → V, LinearIndependent F b ∧ Submodule.span F (Set.range b) = U := by
  let b := Module.finBasis F U
  have h1 : LinearIndependent F (fun k => (b k : V)) := b.linearIndependent.map' U.subtype U.ker_subtype
  have h2 : Submodule.span F (Set.range fun k => (b k : V)) = U := by
    have := congrArg (Submodule.map U.subtype) b.span_eq
    rwa [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top] at this
  have h3 := hj.2 _ _ h1
  have h4 : Submodule.span Ω (Set.range fun k => j (b k : V)) = U' := by
    rw [h]
    refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨k, rfl⟩
      exact ⟨_, (b k).2, rfl⟩
    · rintro _ ⟨e, he, rfl⟩
      rw [← h2] at he
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 he
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [hj.1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have h5 : Module.finrank F U = n := by
    have := finrank_span_eq_card h3
    rw [h4, Module.finrank_eq_card_basis B, Fintype.card_fin, Fintype.card_fin] at this
    exact this.symm
  subst h5
  exact ⟨_, h1, h2⟩

end PositivityTheory.Xgp.FlagsLieBaseChange

open PositivityTheory.Xgp.FlagsLieBaseChange in
theorem PositivityTheory.Xgp.exists_flags_lie_compact_dominated : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) (x : (Σ k, J k) → Ω) (A : HodgeCpt Y S x) (F₀ : Type) [Field F₀] (ξ₀ : Spec (CommRingCat.of F₀) ⟶ Y.X) (ι : F₀ →+* Ω), IsCptGen ξ₀ → GlobalTheory.CompanionTheory.Ar.Dominates A.ξ ξ₀ A.f ι → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module F₀ Li₀) (M₀ : LieModel Y.t.G ξ₀ Li₀) (j₁ : Li₀ →+ A.Li) (V₀ : CMType H ⊕ CMType H → Submodule F₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li₀), (∀ e, (A.M.pt (j₁ e)).left ≫ A.m.φ = spMap (dualMap ι) ≫ (M₀.pt e).left) ∧ IsExtOver ι j₁ ∧ (∀ s e, e ∈ V₀ s ↔ j₁ e ∈ A.Vgen s) ∧ ∀ s, LinearIndependent F₀ (b s) ∧ Submodule.span F₀ (Set.range (b s)) = V₀ s := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J x A F₀ _ ξ₀ ι hgen hd
  obtain ⟨Li₀, _, _, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ Y.t.G F₀ ξ₀
  obtain ⟨ρ₀, hact₀, -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act _ Y.t.G F₀ ξ₀ Li₀ M₀ (𝓞 E) Y.t.act.act
    Y.t.act.hom Y.t.act.one Y.t.act.mul Y.t.act.add
  obtain ⟨j, hj, hext, hsp, hfin⟩ := bc Y.t.semi.smooth ι ξ₀ (A.ξ ≫ A.f) (Eq.symm hd) M₀
    (LieMove.pushModel A.m.cart A.M)
  have hj' : ∀ e, (A.M.pt (j e)).left ≫ A.m.φ = spMap (dualMap ι) ≫ (M₀.pt e).left := hj
  have hint := FlagStep.lieMap_act_pull E H Y.X A.X Y.t A.t A.f A.m F₀ Ω ξ₀ A.ξ ι Li₀ A.Li M₀ A.M ρ₀ A.ρ j hd hact₀
    A.act hj'
  have hjinj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).2 fun e he => ?_
    by_contra hne
    have h1 := hext.2 1 (fun _ => e) (LinearIndependent.of_subsingleton (0 : Fin 1) hne)
    exact h1.ne_zero (0 : Fin 1) he
  let a : 𝓞 c.F →+* F₀ := (Spec.preimage (ξ₀ ≫ Y.s)).hom
  have ha : spMap a = ξ₀ ≫ Y.s := by
    simp only [spMap, a, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hfa : ι.comp a = A.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have h1 : spMap (ι.comp a) = spMap (A.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← A.cst_over]
      have hd' : A.ξ ≫ A.f = spMap ι ≫ ξ₀ := hd
      calc spMap (ι.comp a) = spMap ι ≫ spMap a := by
            simp only [spMap, ← Spec.map_comp]; rfl
        _ = A.ξ ≫ A.f ≫ Y.s := by rw [ha, ← Category.assoc, ← hd', Category.assoc]
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hainj : Function.Injective a := by
    have : Function.Injective (ι.comp a) := by
      rw [hfa]
      exact A.cst.injective.comp (IsFractionRing.injective (𝓞 c.F) c.F)
    exact Function.Injective.of_comp (f := ι) this
  let a' : c.F →+* F₀ := IsFractionRing.lift hainj
  have ha' : ι.comp a' = A.cst := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) ?_
    rw [← hfa]
    refine RingHom.ext fun o => ?_
    exact congrArg ι (IsFractionRing.lift_algebraMap hainj o)
  haveI : CharZero F₀ := ι.charZero
  let σ : CMType H ⊕ CMType H → (𝓞 E →+* F₀) := fun s => a'.comp (labelEmb c s)
  have hσ : ∀ s, A.emb s = ι.comp (σ s) := fun s => by
    rw [← RingHom.comp_assoc, ha']
    rfl
  have hV : ∀ s, A.Vgen s = Submodule.span Ω (j '' (eigSp ρ₀ (σ s) : Set Li₀)) := fun s => by
    unfold HodgeCpt.Vgen
    rw [hσ]
    exact EigExt.eigSp_ext E F₀ Ω ι Li₀ A.Li j ρ₀ A.ρ (σ s) hext hsp fun a e => (hint a e).symm
  have hb := fun s => basis hext _ _ (hV s) (nonempty_basis_Vgen A s).some
  choose b hb using hb
  refine ⟨Li₀, inferInstance, inferInstance, M₀, j, fun s => eigSp ρ₀ (σ s), b, hj', hext, fun s e => ?_, hb⟩
  unfold HodgeCpt.Vgen
  rw [hσ]
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun a => ?_
  rw [← hint a e, RingHom.comp_apply ι, ← hext.1]
  exact hjinj.eq_iff.symm
end

