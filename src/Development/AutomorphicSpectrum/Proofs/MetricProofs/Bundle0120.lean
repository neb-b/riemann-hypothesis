module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0116
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0084
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0088
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0092
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0111
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0021
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagMinorTrdeg
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0110

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartHolomorphicComposition
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem lift_analyticAt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {n e : ℕ}
    (R : AnLogRes P J n) {V : Set (Fin e → ℂ)} {bp : (Fin e → ℂ) → R.X} (hV : IsOpen V) (hc : ContinuousOn bp V)
    (ha : ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ bp) (V ∩ bp ⁻¹' (R.A.chart k).source)) {u₀ : Fin e → ℂ} (hu : u₀ ∈ V)
    (p : Σ k, ι k) : AnalyticAt ℂ (fun u => R.lift (bp u₀) (bp u) p) u₀ := by
  obtain ⟨k, hk⟩ := R.A.cover (bp u₀)
  have h1 : AnalyticAt ℂ (R.A.chart k ∘ bp) u₀ := ha k u₀ ⟨hu, hk⟩
  have h2 : AnalyticAt ℂ ((fun y => R.lift (bp u₀) y p) ∘ (R.A.chart k).symm) ((R.A.chart k ∘ bp) u₀) :=
    R.holo (bp u₀) p k _ ⟨(R.A.chart k).map_source hk, by
      show (R.A.chart k).symm (R.A.chart k (bp u₀)) ∈ R.U (bp u₀)
      rw [(R.A.chart k).left_inv hk]
      exact R.mem_U _⟩
  refine (h2.comp h1).congr ?_
  have hW : V ∩ bp ⁻¹' (R.A.chart k).source ∈ 𝓝 u₀ :=
    (hc.isOpen_inter_preimage hV (R.A.chart k).open_source).mem_nhds ⟨hu, hk⟩
  filter_upwards [hW] with u hu'
  simp only [Function.comp, (R.A.chart k).left_inv hu'.2]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem bvec_analyticAt {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) {e : ℕ}
    {V : Set (Fin e → ℂ)} {bp : (Fin e → ℂ) → BM.Rb.X} (hV : IsOpen V) (hc : ContinuousOn bp V)
    (ha : ∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source))
    (hO : ∀ u ∈ V, bp u ∈ BM.O l) {u₀ : Fin e → ℂ} (hu : u₀ ∈ V) (q : Σ k, baseIdx ι M.blk k) :
    AnalyticAt ℂ (fun u => FC.bvec BM l (bp u) q) u₀ := by
  have hne : BM.Rb.lift (bp u₀) (bp u₀) ⟨q.1, (BM.F l).c q.1⟩ ≠ 0 :=
    FibreCount.chart_ne ((BM.good l _ (hO u₀ hu)).1 q.1)
  have hq := (lift_analyticAt BM.Rb hV hc ha hu q).div
    (lift_analyticAt BM.Rb hV hc ha hu ⟨q.1, (BM.F l).c q.1⟩) hne
  refine hq.congr ?_
  have hW : V ∩ bp ⁻¹' (BM.Rb.U (bp u₀)) ∈ 𝓝 u₀ :=
    (hc.isOpen_inter_preimage hV (BM.Rb.isOpen_U _)).mem_nhds ⟨hu, BM.Rb.mem_U _⟩
  filter_upwards [hW] with u hu'
  obtain ⟨c, hc0, ec⟩ := BM.Rb.compat (bp u₀) (bp u) (bp u) ⟨hu'.2, BM.Rb.mem_U _⟩
  show BM.Rb.lift (bp u₀) (bp u) q / BM.Rb.lift (bp u₀) (bp u) ⟨q.1, (BM.F l).c q.1⟩ =
    BM.Rb.lift (bp u) (bp u) q / BM.Rb.lift (bp u) (bp u) ⟨q.1, (BM.F l).c q.1⟩
  rw [ec]
  exact mul_div_mul_left _ _ (hc0 q.1)

theorem valAt_analyticAt {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) {e : ℕ}
    {V : Set (Fin e → ℂ)} {bp : (Fin e → ℂ) → BM.Rb.X} (hV : IsOpen V) (hO : ∀ u ∈ V, bp u ∈ BM.O l)
    {u₀ : Fin e → ℂ} (hu : u₀ ∈ V) (hw : ∀ q, AnalyticAt ℂ (fun u => FC.bvec BM l (bp u) q) u₀) {s : M.Ω}
    (hs : RegAt M.x (mCoordIdeal (FC.bvec BM l (bp u₀))) s) :
    AnalyticAt ℂ (fun u => valAt M.x s (FC.bvec BM l (bp u))) u₀ := by
  obtain ⟨d, g, h, hg, hh, hQ, eq⟩ := hs
  have hE : ∀ (z : (Σ k, baseIdx ι M.blk k) → ℂ) (f : MRing (baseIdx ι M.blk)),
      eval z (map (Int.castRingHom ℂ) f) = aeval z f := fun z f => by
    rw [aeval_def, algebraMap_int_eq, ← eval_map]
  have aG : AnalyticAt ℂ (fun u => aeval (FC.bvec BM l (bp u)) g) u₀ := AnalyticAt.aeval_mvPolynomial hw g
  have aH : AnalyticAt ℂ (fun u => aeval (FC.bvec BM l (bp u)) h) u₀ := AnalyticAt.aeval_mvPolynomial hw h
  have h0 : aeval (FC.bvec BM l (bp u₀)) h ≠ 0 := fun e0 => hQ (mem_mCoordIdeal_of_aeval_eq_zero _ hh e0)
  refine (aG.div aH h0).congr ?_
  filter_upwards [hV.mem_nhds hu, aH.continuousAt.eventually_ne h0] with u hu' hne
  have hz := (bvec_good K ι Φ y Ψ N j M n BM l _ (hO u hu')).1
  have h1 : eval (FC.bvec BM l (bp u)) (map (Int.castRingHom ℂ) h) ≠ 0 := by rwa [hE]
  have h2 : aeval M.x h ≠ 0 := fun e0 => h1 (hz.2 h (mem_mCoordIdeal_of_aeval_eq_zero M.x hh e0))
  have hv : IsValueAt M.x s (FC.bvec BM l (bp u))
      (eval (FC.bvec BM l (bp u)) (map (Int.castRingHom ℂ) g) / eval (FC.bvec BM l (bp u)) (map (Int.castRingHom ℂ) h)) :=
    ⟨d, g, h, hg, hh, h2, eq, h1, rfl⟩
  rw [valAt_eq hz hv, hE, hE]
  rfl

theorem bvec_val_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q) (e : ℕ) (V : Set (Fin e → ℂ)) (bp : (Fin e → ℂ) → BM.Rb.X), IsOpen V → ContinuousOn bp V → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) → (∀ u ∈ V, bp u ∈ BM.O l) → (∀ q, AnalyticOnNhd ℂ (fun u => FC.bvec BM l (bp u) q) V) ∧ ∀ s : M.Ω, (∀ b ∈ BM.O l, RegAt M.x (mCoordIdeal (FC.bvec BM l b)) s) → AnalyticOnNhd ℂ (fun u => valAt M.x s (FC.bvec BM l (bp u))) V := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l e V bp hV hc ha hO
  have hb : ∀ q, AnalyticOnNhd ℂ (fun u => FC.bvec BM l (bp u) q) V := fun q u hu =>
    bvec_analyticAt BM l hV hc ha hO hu q
  exact ⟨hb, fun s hs u hu => valAt_analyticAt BM l hV hO hu (fun q => hb q u hu) (hs _ (hO u hu))⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFlagPointInOrbit
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

private theorem sameOrbit_symm_metric {K : Type} {ι : K → Type} {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  show z' p = (c p.1)⁻¹ * (c p.1 * z' p)
  rw [← mul_assoc, inv_mul_cancel₀ (hc p.1), one_mul]

private theorem sameOrbit_trans_metric {K : Type} {ι : K → Type} {z z' z'' : (Σ k, ι k) → ℂ}
    (h1 : SameOrbit z z') (h2 : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h1
  obtain ⟨d, hd, rfl⟩ := h2
  refine ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), ?_⟩
  funext p
  show c p.1 * (d p.1 * z'' p) = c p.1 * d p.1 * z'' p
  rw [mul_assoc]

theorem exists_flagPt_of_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ z ∈ mcPts (mCoordIdeal y), SameOrbit (basePart M.blk z) (BM.Rb.lift b b) → ∃ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) ∧ SameOrbit z (FC.flagPt M (BM.F l) (FC.bvec BM l b) h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb z hz hzb
  obtain ⟨hβmem, hβgood, hβc, hβorb⟩ := bvec_good K ι Φ y Ψ N j M n BM l b hb
  have h1 : SameOrbit (basePart M.blk z) (bvec BM l b) :=
    sameOrbit_trans_metric hzb (sameOrbit_symm_metric hβorb)
  obtain ⟨d, hd, hdz⟩ := id h1
  have hne : ∀ k, basePart M.blk z ⟨k, (BM.F l).c k⟩ ≠ 0 := by
    intro k
    rw [hdz]
    show d k * bvec BM l b ⟨k, (BM.F l).c k⟩ ≠ 0
    rw [hβc k, mul_one]
    exact hd k
  obtain ⟨z₁, hz₁z, hz₁c⟩ := GlobalTheory.CompanionTheory.Ar.PB.FibreCount.exists_normal_base M.blk (BM.F l).c z hne
  have hb1 : SameOrbit (basePart M.blk z₁) (bvec BM l b) :=
    sameOrbit_trans_metric (GlobalTheory.CompanionTheory.Ar.PB.FibreCount.basePart_orbit M.blk hz₁z) h1
  have hbeq : basePart M.blk z₁ = bvec BM l b := by
    obtain ⟨e, he, hez⟩ := hb1
    have he1 : ∀ k, e k = 1 := by
      intro k
      have hk := congrFun hez ⟨k, (BM.F l).c k⟩
      have hk' : basePart M.blk z₁ ⟨k, (BM.F l).c k⟩ = e k * bvec BM l b ⟨k, (BM.F l).c k⟩ := hk
      rw [hz₁c k, hβc k, mul_one] at hk'
      exact hk'.symm
    rw [hez]
    funext p
    show e p.1 * bvec BM l b p = bvec BM l b p
    rw [he1, one_mul]
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y) := by
    obtain ⟨c, hc, hcz⟩ := id hz₁z
    refine ⟨?_, ?_⟩
    · intro k
      obtain ⟨i, hi⟩ := hz.1 k
      refine ⟨i, ?_⟩
      rw [hcz]
      exact mul_ne_zero (hc k) hi
    · intro f hf
      have hf' : f ∈ mCoordIdeal z₁ := by
        rw [GlobalTheory.CompanionTheory.Ar.PB.FibreCount.mCoordIdeal_eq_of_orbit hz₁z]
        exact GlobalTheory.CompanionTheory.Ar.PB.CPts.mCoordIdeal_le hz hf
      exact eval_eq_zero_of_mem_mCoordIdeal hf'
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk z₁)) := by
    rw [hbeq]
    exact hβgood
  obtain ⟨h, hflag⟩ := GlobalTheory.CompanionTheory.Ar.PB.CPts.flag_fwd M (BM.isFrame l) hz₁ hgood hz₁c
  obtain ⟨_, hhb, hblocks⟩ := hflag
  refine ⟨h, hhb, ?_⟩
  have h2 : SameOrbit z₁ (flagPt M (BM.F l) (bvec BM l b) h) := by
    apply GlobalTheory.CompanionTheory.Ar.PB.FibreCount.sameOrbit_of_blocks M.blk
    · rw [basePart_flagPt, hbeq]
    · intro p k hpk
      obtain ⟨a, ha, hza⟩ := hblocks p k hpk
      refine ⟨a, ha, fun m => ?_⟩
      rw [hza m, flagPt_step M (BM.F l) (bvec BM l b) h hpk m, hbeq]
  exact sameOrbit_trans_metric (sameOrbit_symm_metric hz₁z) h2

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietyFirst
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.WMem

section Mat

variable {N j : ℕ}

theorem transv_isBlockDiag {a b ca cb : Fin N} (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  have same : ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) := by
    have := a.2
    have := b.2
    have := cb.2
    unfold lastCol at hca
    split_ifs at hca <;> omega
  intro r s hrs
  have e1 : r ≠ s := fun e => hrs (by rw [e])
  rw [Matrix.add_apply, Matrix.one_apply_ne e1, zero_add, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hrs same.symm

theorem transv_det_one {ca cb : Fin N} (hc : (cb : ℕ) = ca + 1) (t : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 := by
  have hne : ca ≠ cb := fun e => by rw [e] at hc; omega
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  rw [Matrix.det_of_lowerTriangular _ fun r c h => ?_]
  · refine Finset.prod_eq_one fun c _ => ?_
    rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, e⟩
    exact hne e
  · have h' : r < c := h
    rw [Matrix.add_apply, Matrix.one_apply_ne h'.ne, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm h' hlt

end Mat

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem isFlagOf_flagPt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {b : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : ∀ k, b ⟨k, F.c k⟩ = 1) {h : Ψ → Matrix (Fin N) (Fin N) ℂ}
    (hh : ∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0) : M.IsFlagOf F (flagPt M F b h) h := by
  refine ⟨fun k => by rw [basePart_flagPt]; exact hb k, hh, fun p k hp => ⟨1, one_ne_zero, fun m => ?_⟩⟩
  rw [basePart_flagPt, flagPt_step M F b h hp m, one_mul]

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (l : Fin BM.q), ∀ b' ∈ BM.O l, ∀ (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) → FC.wVec M (BM.F l) (FC.bvec BM l b') h τ a k₀ ca cb t ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM d τ a b k₀ ca cb hb hab hk hca hcb hvar l b' hb' h t hh
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.fstPt_sndPt_wVec K ι Φ y Ψ N j M τ a b k₀ ca cb hb hab hk hca hcb (BM.F l) (bvec BM l b') h t
  obtain ⟨g1, g2, g3, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good K ι Φ y Ψ N j M n BM l b' hb'
  have hh' : ∀ τ', IsBlockDiag j (Function.update h τ (h τ * (1 + Matrix.single cb ca t)) τ') ∧
      (Function.update h τ (h τ * (1 + Matrix.single cb ca t)) τ').det ≠ 0 := by
    intro τ'
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      refine ⟨(hh τ').1.mul (transv_isBlockDiag hb hab hca hcb t), ?_⟩
      rw [Matrix.det_mul, transv_det_one hcb, mul_one]
      exact (hh τ').2
    · rw [Function.update_of_ne e]
      exact hh τ'
  have hbase : basePart M.blk (fstPt k₀ (wVec M (BM.F l) (bvec BM l b') h τ a k₀ ca cb t)) = bvec BM l b' := by
    rw [h1, basePart_flagPt]
  refine (_root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts.main K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hvar (BM.F l) _ (BM.isFrame l)
    (by rw [hbase]; exact g1) (by rw [hbase]; exact g2) (by rw [hbase]; exact g3)).2 ⟨h, t, ?_, ?_⟩
  · rw [h1]
    exact isFlagOf_flagPt M (BM.F l) g3 hh
  · rw [h2]
    exact isFlagOf_flagPt M (BM.F l) g3 hh'

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.WMem
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietySecond
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem exists_flags_of_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (l : Fin BM.q), ∀ b' ∈ BM.O l, ∀ z ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)), SameOrbit (basePart M.blk (fstPt k₀ z)) (BM.Rb.lift b' b') → ∃ (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) ∧ SameOrbit z (FC.wVec M (BM.F l) (FC.bvec BM l b') h τ a k₀ ca cb t) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM d τ a b k₀ ca cb hb hj hblk hca hcb hy l b' hb' z hz ho
  obtain ⟨g1, g2, g3, g4⟩ := FC.bvec_good K ι Φ y Ψ N j M n BM l b' hb'
  set β := FC.bvec BM l b' with hβ
  obtain ⟨c, hc, ec⟩ : SameOrbit (basePart M.blk (fstPt k₀ z)) β := orbit_trans ho (orbit_symm g4)
  let t : Option K → ℂ := fun o => match o with
    | some k => if hk : ∀ p, M.blk p ≠ some k then (c ⟨k, hk⟩)⁻¹ else 1
    | none => 1
  have ht : ∀ o, t o ≠ 0 := fun o => by
    cases o with
    | none => exact one_ne_zero
    | some k =>
      by_cases hk : ∀ p, M.blk p ≠ some k
      · simp only [t, dif_pos hk]
        exact inv_ne_zero (hc _)
      · simp only [t, dif_neg hk]
        exact one_ne_zero
  let z₁ : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun p => t p.1 * z p
  have o2 : SameOrbit z₁ z := ⟨t, ht, rfl⟩
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) :=
    mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) o2 hz
  have eb : basePart M.blk (fstPt k₀ z₁) = β := by
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    have e : z ⟨some k, m⟩ = c ⟨k, hk⟩ * β ⟨⟨k, hk⟩, m⟩ := congrFun ec ⟨⟨k, hk⟩, m⟩
    show t (some k) * z ⟨some k, m⟩ = β _
    simp only [t, dif_pos hk]
    rw [e, inv_mul_cancel_left₀ (hc _)]
  have P := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts.main K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hj hblk hca hcb hy (BM.F l) z₁ (BM.isFrame l)
    (by rw [eb]; exact g1) (by rw [eb]; exact g2) (by rw [eb]; exact g3)
  obtain ⟨h, s, f1, f2⟩ := P.1 hz₁
  refine ⟨h, s, f1.2.1, orbit_trans (orbit_symm o2) ?_⟩
  have eb2 : basePart M.blk (sndPt k₀ z₁) = β := by
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    have hne : k ≠ k₀ := fun e => hk (τ, a) (by rw [hblk, e])
    have e1 : sndPt k₀ z₁ ⟨k, m⟩ = fstPt k₀ z₁ ⟨k, m⟩ := by
      show z₁ (v₁ k₀ ⟨k, m⟩) = z₁ (v₀ k₀ ⟨k, m⟩)
      rw [v₁_ne hne]
      rfl
    exact e1.trans (congrFun eb ⟨⟨k, hk⟩, m⟩)
  have key : ∀ o : Option K, ∃ e : ℂ, e ≠ 0 ∧ ∀ m : ι (o.getD k₀),
      z₁ ⟨o, m⟩ = e * FC.wVec M (BM.F l) β h τ a k₀ ca cb s ⟨o, m⟩ := fun o => by
    cases o with
    | none =>
      obtain ⟨e, he, w⟩ := f2.2.2 (τ, a) k₀ hblk
      refine ⟨e, he, fun m => ?_⟩
      have w' := w m
      rw [eb2] at w'
      simp only [Function.update_self] at w'
      have e1 : sndPt k₀ z₁ ⟨k₀, m⟩ = z₁ ⟨none, m⟩ := by
        show z₁ (v₁ k₀ ⟨k₀, m⟩) = _
        rw [v₁_self]
      rw [← e1, w']
      rfl
    | some k =>
      by_cases hk : ∀ p, M.blk p ≠ some k
      · refine ⟨1, one_ne_zero, fun m => ?_⟩
        have e1 := congrFun eb ⟨⟨k, hk⟩, m⟩
        have e2 := congrFun (FC.basePart_flagPt M (BM.F l) β h) ⟨⟨k, hk⟩, m⟩
        show z₁ ⟨some k, m⟩ = 1 * FC.flagPt M (BM.F l) β h ⟨k, m⟩
        rw [one_mul]
        exact e1.trans e2.symm
      · push_neg at hk
        obtain ⟨p, hp⟩ := hk
        obtain ⟨e, he, w⟩ := f1.2.2 p k hp
        refine ⟨e, he, fun m => ?_⟩
        have w' := w m
        rw [eb] at w'
        show z₁ ⟨some k, m⟩ = e * FC.flagPt M (BM.F l) β h ⟨k, m⟩
        rw [FC.flagPt_step M (BM.F l) β h hp m]
        exact w'
  choose e he hm using key
  exact ⟨e, he, funext fun q => hm q.1 q.2⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsBaseMetric
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → BM.Rb.X) (hc : Continuous pr), IsWAtlas M BM.Rb τ a k₀ ca cb RW pr → ∃ (L' : LocPot RW.X) (v : RW.X → RW.X → ℂ) (Dg : Set RW.X) (cst : ℝ), IsPotential RW.A L' ∧ IsSection RW.A L' v ∧ IsSNC RW.A L' v ![1] ![Dg] ∧ IsSNC RW.A (BM.L.pullback pr hc + L') (fun x y => BM.s (pr x) (pr y) * v x y) (Fin.snoc BM.m 1) (Fin.snoc (fun k => pr ⁻¹' BM.W k) Dg) ∧ (∀ w, logNormSec L' v w ≤ 0) ∧ IsNormFn M τ a k₀ ca cb RW fun x => logNormSec L' v x + cst := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM τ a b k₀ ca cb hb hj hblk hca hcb _ RW pr hc hW
  choose ψ kb σ i₀ V u hL using
    _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen.main K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a b k₀ ca cb hb hj hblk hca hcb RW pr hW
  obtain ⟨c, hc0⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.logNormSec_secPot_le K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL hblk hW
  refine ⟨GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.secPot RW (GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.potA M τ a k₀) V
      (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c,
    GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec ψ i₀ u, GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSet k₀ RW, c, ?_, ?_, ?_, ?_, hc0, ?_⟩
  · exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isPotential_secPot K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL c
  · exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isSection_diagSec K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL hblk hW c
  · exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec_isSNC_diagSet K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL c
  · exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.SncProd.main K ι Φ y Ψ N j M n (d + 2) BM τ a k₀ ca cb RW pr hc ψ kb σ i₀ V u hL hW.1 c
  · exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isNormFn_logNormSec_diagSec K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL b hb hj hblk hca hcb hW c

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverDegreeOneRealisation
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem identity_cover : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), ∃ (Cv : FlagCover M M) (CR : CovReal FA Cv), Cv.deg = 1 ∧ (∀ p, CR.Re.ref p = FA.Re.ref (some p)) ∧ ∀ p t, CR.Re.line p t = FA.Re.line (some p) t := by
  exact @PositivityTheory.Xgp.t_c_cov_self

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointInMultiprojectivePoints
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem flagPt_mem_mcPts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) → FC.flagPt M (BM.F l) (FC.bvec BM l b) h ∈ mcPts (mCoordIdeal y) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb h hh
  obtain ⟨hmem, hgood, hnorm, -⟩ := FC.bvec_good K ι Φ y Ψ N j M n BM l b hb
  have e := basePart_flagPt M (BM.F l) (FC.bvec BM l b) h
  refine CPts.flag_back M (BM.isFrame l) (by rw [e]; exact hmem) (by rw [e]; exact hgood) (h := h)
    ⟨fun k => by rw [e]; exact hnorm k, hh, fun p k hp => ⟨1, one_ne_zero, fun m => ?_⟩⟩
  rw [e, one_mul]
  exact flagPt_step M (BM.F l) (FC.bvec BM l b) h hp m

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PushDownOfArithIntersectionSystem
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv


open GroundTheory.Heights₂.Heights.LowerBoundFree in
theorem hodgeFlagArith : HodgeFlagArith.Statement :=
  HodgeFlagArith.proof HodgeFlagNeZero.proof
    (HodgeFlagRatioTrdeg.proof HodgeFlagRatioFieldEq.full HodgeFlagMinorTrdeg.proof)

theorem pushDown :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement →
      GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.Statement := fun h =>
  GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.proof (GlobalTheory.T.generic_degree_of_arith_system h) GlobalTheory.CompanionTheory.Ar.Giv.ProjF.pfStep hodgeFlagArith

end GlobalTheory.CompanionTheory.Ar.Giv
end

