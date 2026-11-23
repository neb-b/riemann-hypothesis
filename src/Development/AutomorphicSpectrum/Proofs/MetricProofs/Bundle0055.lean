module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0051

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartFlagAnalyticMap
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem contDiffOn_gram_comp_basePoint :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n)  (l : Fin BM.q) (τ' : Ψ) (Un : Set (Fin d → ℂ)) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → ContinuousOn bp Un → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) → (∀ w ∈ Un, bp w ∈ BM.O l \ bdry BM.s) → ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => BM.G l τ' (bp w) r s) Un := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM l τ' Un bp hU hbp han hmem r t
  have hre := contDiffOn_comp_of_analytic_in_charts _ _ _ BM.Rb.A Un bp _ _ hU hbp han hmem
    (BM.G_smooth l τ' r t).1
  have him := contDiffOn_comp_of_analytic_in_charts _ _ _ BM.Rb.A Un bp _ _ hU hbp han hmem
    (BM.G_smooth l τ' r t).2
  have h1 := Complex.ofRealCLM.contDiff.comp_contDiffOn hre
  have h2 := Complex.ofRealCLM.contDiff.comp_contDiffOn him
  have h3 := h1.add (h2.mul (contDiffOn_const (c := Complex.I)))
  refine h3.congr ?_
  intro w _
  simp [Complex.re_add_im]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMapFrameRestriction
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem exists_section (M : FlagModel y Ψ N j) {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v)
    (hr : ∀ k : NonPluckerBlocks M.blk, k.1 ∈ Set.range κ) :
    ∃ (κ' : NonPluckerBlocks M.blk → Kk) (v' : (Σ k, baseIdx ι M.blk k) → (Σ k, ιk k)), IsBlockMap κ' v' ∧
      (∀ q, v (v' q) = ⟨q.1.1, q.2⟩) ∧ ∀ z, pBase M v z = z ∘ v' := by
  choose κ' hκ' using hr
  have hex : ∀ q : Σ k, baseIdx ι M.blk k, ∃ q', v q' = ⟨q.1.1, q.2⟩ := fun q =>
    hb.2.2.2 ⟨q.1.1, q.2⟩ ⟨κ' q.1, hκ' q.1⟩
  choose v' hv' using hex
  have hfst : ∀ p, (v' p).1 = κ' p.1 := fun p => hb.1 (by
    rw [← hb.2.2.1, hv', hκ'])
  refine ⟨κ', v', ⟨fun a b e => Subtype.ext (by rw [← hκ' a, ← hκ' b, e]), fun a b e => ?_, hfst, ?_⟩, hv', fun z => ?_⟩
  · have e' := congrArg v e
    rw [hv', hv'] at e'
    exact (GlobalTheory.CompanionTheory.Ar.PB.CPts.blockMap_base M).2.1 e'
  · rintro q ⟨kb, hq⟩
    have h1 : (v q).1 ∈ Set.range (Subtype.val : NonPluckerBlocks M.blk → K) :=
      ⟨kb, by rw [hb.2.2.1, ← hq, hκ']⟩
    obtain ⟨p, hp⟩ := (GlobalTheory.CompanionTheory.Ar.PB.CPts.blockMap_base M).2.2.2 (v q) h1
    exact ⟨p, hb.2.1 ((hv' p).trans hp)⟩
  · funext q
    show upV v z ⟨q.1.1, q.2⟩ = z (v' q)
    rw [← hv', upV_apply hb.2.1]

end

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → (∀ z ∈ mcPts (mCoordIdeal (y ∘ v)), pBase M v z ∈ mcPts (mCoordIdeal M.x)) ∧ ∀ z z' : (Σ k, ιk k) → ℂ, SameOrbit z z' → SameOrbit (pBase M v z) (pBase M v z') := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M keep Kk _ ιk _ κ v hb hk
  obtain ⟨κ', v', hb', hv', hz⟩ := exists_section M hb fun k => (hk k.1).2 (Or.inl k.2)
  refine ⟨fun z hzm => ?_, fun z z' ho => ?_⟩
  · rw [hz]
    refine GlobalTheory.CompanionTheory.Ar.PB.CPts.comp_mem_mcPts hb' (algebraMap M.Ω Φ) (funext fun q => ?_) hzm
    show y (v (v' q)) = algebraMap M.Ω Φ (M.x q)
    rw [hv']
    exact M.y_base q
  · obtain ⟨c, hc, e⟩ := ho
    refine ⟨fun k => c (κ' k), fun k => hc _, ?_⟩
    rw [hz, hz, e]
    funext q
    show c (v' q).1 * z' (v' q) = c (κ' q.1) * z' (v' q)
    rw [hb'.2.2.1]

end GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricGrassmannChartLocal
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.FlagPoint

theorem stepCols_ne_empty {N j : ℕ} (hj : j ≤ N) (i : Fin N) : stepCols N j i ≠ ∅ := by
  intro h
  have hi' := i.2
  by_cases hi : (i : ℕ) + 1 ≤ j
  · have hm : (⟨N - j, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hi]
      constructor <;> simp
    simp [h] at hm
  · have hm : (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hi]
      show 0 < (i : ℕ) + 1 - j
      omega
    simp [h] at hm

theorem val_sum {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {α : Type} (s : Finset α)
    (f : α → Ω) (hf : ∀ a ∈ s, RegAt x (mCoordIdeal z) (f a)) :
    RegAt x (mCoordIdeal z) (∑ a ∈ s, f a) ∧ valAt x (∑ a ∈ s, f a) z = ∑ a ∈ s, valAt x (f a) z := by
  have R := GlobalTheory.CompanionTheory.Ar.PB.ValRing.regAt_valAt_ring K ι Ω x z hz
  induction s using Finset.induction_on with
  | empty => simpa using ⟨R.1, R.2.2.1⟩
  | insert a s ha ih =>
    have ih' := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    have h := R.2.2.2.2 (f a) _ (hf a (Finset.mem_insert_self _ _)) ih'.1
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨h.2.1, h.2.2.2.trans (by rw [ih'.2])⟩

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ)
    (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ),
    M.blk p = some k₀ → x₀ ∈ BM.O l → z ∈ mcPts (mCoordIdeal y) →
    SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) →
    ∃ (h : Matrix (Fin N) (Fin N) ℂ) (a : ℂ), IsBlockDiag j h ∧ h.det ≠ 0 ∧ a ≠ 0 ∧
      (∀ I, IsStepRows N j p.2 I → plk M (BM.F l) k₀ z I = a * minorIJ h I (stepCols N j p.2)) ∧
      ∀ m : ι k₀, z ⟨k₀, m⟩ =
        a * ∑ I, valAt M.x ((BM.F l).u ⟨k₀, m⟩ I) (basePart M.blk z) * minorIJ h I (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p k₀ l x₀ z hblk hx hz horb
  obtain ⟨F, hFe⟩ : ∃ F, F = BM.F l := ⟨_, rfl⟩
  rw [← hFe]
  have hF : M.IsFrame F := hFe ▸ BM.isFrame l
  have hG₀ : M.GoodAt F (mCoordIdeal (BM.Rb.lift x₀ x₀)) := hFe ▸ BM.good l x₀ hx
  obtain ⟨hp1, -, hp3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.main K ι Φ y Ψ N j M
  obtain ⟨zb, hzbe⟩ : ∃ zb, zb = basePart M.blk z := ⟨_, rfl⟩
  rw [← hzbe] at horb ⊢
  have hzbm : zb ∈ mcPts (mCoordIdeal M.x) := hzbe ▸ hp1 z hz
  obtain ⟨c₀, hc₀, hc₀e⟩ := horb
  have hG : M.GoodAt F (mCoordIdeal zb) := by
    have e : mCoordIdeal zb = mCoordIdeal (BM.Rb.lift x₀ x₀) := by
      rw [hc₀e]
      exact (GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main _ _ _ M.x (BM.Rb.lift x₀ x₀) c₀ hc₀).1
    rw [e]
    exact hG₀
  have hne : ∀ k : NonPluckerBlocks M.blk, zb ⟨k, F.c k⟩ ≠ 0 := fun k h0 => hG.1 k (by
    show mConeMap zb (X ⟨k, F.c k⟩) = 0
    rw [mConeMap, aeval_X, h0, map_zero, zero_mul])
  let c : K → ℂ := fun k =>
    if h : ∀ p', M.blk p' ≠ some k then (zb ⟨⟨k, h⟩, F.c ⟨k, h⟩⟩)⁻¹ else 1
  have hck : ∀ k : NonPluckerBlocks M.blk, c k.1 = (zb ⟨k, F.c k⟩)⁻¹ := fun k => dif_pos k.2
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases h : ∀ p', M.blk p' ≠ some k
    · rw [hck ⟨k, h⟩]
      exact inv_ne_zero (hne ⟨k, h⟩)
    · have : c k = 1 := dif_neg h
      rw [this]
      exact one_ne_zero
  have hck₀ : c k₀ = 1 := dif_neg fun h => h p hblk
  let z₁ : (Σ k, ι k) → ℂ := fun q => c q.1 * z q
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y) := ((GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main K ι Φ y z c hc).2 hz).1
  let cb : NonPluckerBlocks M.blk → ℂ := fun k => c k.1
  have hb₁ : basePart M.blk z₁ = fun q => cb q.1 * zb q := by
    rw [hzbe]
    rfl
  obtain ⟨hT1, hT2⟩ :=
    GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x zb cb fun k => hc k.1
  obtain ⟨-, hval⟩ := hT2 hzbm
  have hG₁ : M.GoodAt F (mCoordIdeal (basePart M.blk z₁)) := by
    rw [hb₁, hT1]
    exact hG
  have hnorm : ∀ k, basePart M.blk z₁ ⟨k, F.c k⟩ = 1 := fun k => by
    rw [hb₁]
    show c k.1 * zb ⟨k, F.c k⟩ = 1
    rw [hck, inv_mul_cancel₀ (hne k)]
  obtain ⟨hh, -, hτ, hstep⟩ := (hp3 F hF z₁ (hp1 z₁ hz₁) hG₁ hnorm).1 hz₁
  obtain ⟨a, ha, hza⟩ := hstep p k₀ hblk
  have hvals : ∀ s, valAt M.x s (basePart M.blk z₁) = valAt M.x s zb := fun s => by
    rw [hb₁]
    exact hval s
  have hzk : ∀ m : ι k₀, z ⟨k₀, m⟩ =
      a * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) zb * minorIJ (hh p.1) I (stepCols N j p.2) := fun m => by
    have e : z₁ ⟨k₀, m⟩ = z ⟨k₀, m⟩ := by
      show c k₀ * _ = _
      rw [hck₀, one_mul]
    have := hza m
    rw [e] at this
    simpa only [hvals] using this
  refine ⟨hh p.1, a, (hτ p.1).1, (hτ p.1).2, ha, fun I hI => ?_, hzk⟩
  have R := GlobalTheory.CompanionTheory.Ar.PB.ValRing.regAt_valAt_ring _ _ _ M.x zb hzbm
  have hδ : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩) zb * valAt M.x (F.u ⟨k₀, m⟩ I') zb = if I = I' then 1 else 0 := by
    intro I' hI'
    have h1 := (val_sum hzbm Finset.univ (fun m : ι k₀ => F.u' I ⟨k₀, m⟩ * F.u ⟨k₀, m⟩ I') fun m _ =>
      (R.2.2.2.2 _ _ (hG.2.1 ⟨k₀, m⟩ I).2 (hG.2.1 ⟨k₀, m⟩ I').1).1).2
    rw [hF.2.2.1 p k₀ hblk I I' hI hI'] at h1
    have h2 : ∀ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩ * F.u ⟨k₀, m⟩ I') zb =
        valAt M.x (F.u' I ⟨k₀, m⟩) zb * valAt M.x (F.u ⟨k₀, m⟩ I') zb := fun m =>
      (R.2.2.2.2 _ _ (hG.2.1 ⟨k₀, m⟩ I).2 (hG.2.1 ⟨k₀, m⟩ I').1).2.2.1
    simp only [h2] at h1
    rw [← h1]
    split_ifs
    · exact R.2.2.2.1
    · exact R.2.2.1
  have hmin : ∀ I', ¬ IsStepRows N j p.2 I' → minorIJ (hh p.1) I' (stepCols N j p.2) = 0 := fun I' hI' =>
    ((_root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j p.2 M.j_le).2.1 (hh p.1) I' (hτ p.1).1 hI').resolve_right
      (stepCols_ne_empty M.j_le p.2)
  have hsum : ∑ I', (∑ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩) zb * valAt M.x (F.u ⟨k₀, m⟩ I') zb) *
      minorIJ (hh p.1) I' (stepCols N j p.2) = minorIJ (hh p.1) I (stepCols N j p.2) := by
    rw [Finset.sum_eq_single I]
    · rw [hδ I hI, if_pos rfl, one_mul]
    · intro I' _ hne'
      by_cases hs : IsStepRows N j p.2 I'
      · rw [hδ I' hs, if_neg (Ne.symm hne'), zero_mul]
      · rw [hmin I' hs, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ I) h
  have hplk : plk M F k₀ z I = ∑ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩) zb * z ⟨k₀, m⟩ := by
    rw [hzbe]
    rfl
  rw [hplk, ← hsum, Finset.mul_sum]
  simp only [hzk, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m _ => ?_
  ring

end GlobalTheory.CompanionTheory.Ar.PB.StepW.FlagPoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CardPIdxEqChoose
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept

variable {Ψ : Type} {N j : ℕ}

theorem stepOf_val' (N j : ℕ) (c : Fin N) :
    (stepOf N j c : ℕ) = if N - j ≤ (c : ℕ) then (c : ℕ) - (N - j) else (c : ℕ) + j := rfl

theorem stepOf_mem' (hj : j ≤ N) (c : Fin N) : c ∈ stepCols N j (stepOf N j c) := by
  have := c.2
  have hv := stepOf_val' N j c
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs at hv ⊢ <;> omega

theorem stepOf_top' (hj : j ≤ N) (c d : Fin N) (hd : d ∈ stepCols N j (stepOf N j c)) : d ≤ c := by
  have := c.2
  have := d.2
  have hv := stepOf_val' N j c
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  rw [Fin.le_def]
  split_ifs at hv hd <;> omega

theorem stepOf_proper' (hj : j ≤ N) {a b : Fin N} (hlt : b < a) (hblk : ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)) :
    IsProperStep N j (stepOf N j b) := by
  have := a.2
  have := b.2
  have h : (b : ℕ) < a := hlt
  have hv := stepOf_val' N j b
  simp only [IsProperStep]
  split_ifs at hv <;> omega

theorem sep_of_all (hj : j ≤ N) {keep : Ψ × Fin N → Prop} (hk : ∀ p, keep p) (q : LowIdx Ψ N j) : Sep keep q :=
  ⟨stepOf N j q.1.2.2, hk _, stepOf_proper' hj q.2.1 q.2.2, stepOf_mem' hj _,
    fun h => absurd (stepOf_top' hj _ _ h) (not_le.2 q.2.1)⟩

theorem card_pIdx_of_all : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (keep : Ψ × Fin N → Prop), j ≤ N →
    (∀ p, keep p) → Nat.card (PIdx j keep) = Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  intro Ψ _ _ N j keep hj hk
  have e : PIdx j keep ≃ LowIdx Ψ N j := Equiv.subtypeUnivEquiv (sep_of_all hj hk)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.card_lowIdx Ψ N j hj]

end GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationAntiholomorphicCharts
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

section Helpers

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem affCoord_eq_of_orbit (p : (k : K) → ι k) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    affCoord p z = affCoord p z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  simp only [affCoord]
  exact mul_div_mul_left _ _ (hc q.1)

theorem affCoord_cj (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) :
    affCoord p (cj z) = cj (affCoord p z) := by
  funext q
  simp [affCoord, cj, map_div₀]

theorem ne_zero_of_orbit_cj {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z (cj z')) {q : Σ k, ι k}
    (hq : z q ≠ 0) : z' q ≠ 0 := by
  obtain ⟨c, -, rfl⟩ := h
  intro h0
  exact hq (by simp [cj, h0])

theorem analyticAt_affCoord {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → (Σ k, ι k) → ℂ} {a : E} (p : (k : K) → ι k)
    (hf : ∀ q, AnalyticAt ℂ (fun y => f y q) a) (h0 : ∀ k, f a ⟨k, p k⟩ ≠ 0) :
    AnalyticAt ℂ (fun y => affCoord p (f y)) a := by
  rw [analyticAt_pi_iff]
  intro q
  exact (hf q).div (hf ⟨q.1, p q.1⟩) (h0 q.1)

theorem analyticAt_star_comp {e : ℕ} {ψ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {w : Fin e → ℂ}
    (h : AnalyticAt ℂ ψ w) : AnalyticAt ℂ (star ∘ ψ ∘ star) (star w) := by
  refine GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 ?_
  have hs : Filter.Tendsto (star : (Fin e → ℂ) → Fin e → ℂ) (𝓝 (star w)) (𝓝 w) := by
    simpa using (continuous_star.tendsto (star w))
  filter_upwards [hs.eventually h.eventually_analyticAt] with v hv
  simpa using hv.differentiableAt.star_star

theorem ker_fderiv_star_comp {e : ℕ} {ψ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {w : Fin e → ℂ}
    (h : DifferentiableAt ℂ ψ w) (hk : (fderiv ℂ ψ w).ker = ⊥) :
    (fderiv ℂ (star ∘ ψ ∘ star) (star w)).ker = ⊥ := by
  rw [h.hasFDerivAt.star_star.fderiv, eq_bot_iff]
  intro v hv
  have hv' : star (fderiv ℂ ψ w (star v)) = 0 := by simpa using hv
  have h1 : fderiv ℂ ψ w (star v) = 0 := by simpa using hv'
  have h2 : star v ∈ (fderiv ℂ ψ w).ker := by simpa using h1
  rw [hk] at h2
  have h3 : star v = 0 := by simpa using h2
  simpa using h3

end Helpers

theorem conj_analytic : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∀ (c : X → X), (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) → Continuous c → ∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source)) := by
  intro K _ ι _ e X _ A P U lift hL c hc hcc j k w hw
  obtain ⟨hUo, hUm, hH, hM, hCp, -, -, hIm⟩ := hL
  obtain ⟨hw1, hw2⟩ := hw
  have hw2' : c ((A.chart j).symm w) ∈ (A.chart k).source := hw2
  generalize hx₀ : (A.chart j).symm w = x₀ at hw2'
  generalize hx₁ : c x₀ = x₁ at hw2'
  choose p hp using (hM x₁ x₁ (hUm x₁)).1
  have hp0 : ∀ b, lift x₀ x₀ ⟨b, p b⟩ ≠ 0 := fun b =>
    ne_zero_of_orbit_cj (hx₁ ▸ hc x₀) (by subst hx₁; exact hp b)
  have hsym₁ : (A.chart k).symm (A.chart k x₁) = x₁ := (A.chart k).left_inv hw2'
  have hψ : AnalyticAt ℂ (fun w' => affCoord p (lift x₁ ((A.chart k).symm w'))) (A.chart k x₁) := by
    refine analyticAt_affCoord p (fun q => ?_) (fun b => ?_)
    · exact hH x₁ q k (A.chart k x₁) ⟨(A.chart k).map_source hw2', by simpa [hsym₁] using hUm x₁⟩
    · simpa [hsym₁] using hp b
  have hker := hIm x₁ p hp k hw2'
  have hHa : AnalyticAt ℂ (fun y => affCoord p (lift x₀ ((A.chart j).symm y))) w := by
    refine analyticAt_affCoord p (fun q => ?_) (fun b => ?_)
    · exact hH x₀ q j w ⟨hw1, by simpa [Set.mem_preimage, hx₀] using hUm x₀⟩
    · simpa [hx₀] using hp0 b
  have hsc : ContinuousAt (A.chart j).symm w := (A.chart j).continuousAt_symm hw1
  have hcs : ContinuousAt (fun y => c ((A.chart j).symm y)) w := hcc.continuousAt.comp hsc
  have hFc : ContinuousAt (fun z => star (A.chart k (c ((A.chart j).symm z)))) w := by
    have h1 : ContinuousAt (A.chart k) (c ((A.chart j).symm w)) := by
      rw [hx₀, hx₁]; exact (A.chart k).continuousAt hw2'
    exact continuous_star.continuousAt.comp (ContinuousAt.comp (f := fun y => c ((A.chart j).symm y)) h1 hcs)
  have hFw : star (A.chart k (c ((A.chart j).symm w))) = star (A.chart k x₁) := by
    rw [hx₀, hx₁]
  have e1 : ∀ᶠ y in 𝓝 w, (A.chart j).symm y ∈ U x₀ :=
    hsc ((hUo x₀).mem_nhds (by rw [hx₀]; exact hUm x₀))
  have e2 : ∀ᶠ y in 𝓝 w, c ((A.chart j).symm y) ∈ (A.chart k).source ∩ U x₁ :=
    hcs (((A.chart k).open_source.inter (hUo x₁)).mem_nhds (by
      change c ((A.chart j).symm w) ∈ _
      rw [hx₀, hx₁]; exact ⟨hw2', hUm x₁⟩))
  refine GlobalTheory.T.analytic_of_immersion_composition (fun z => star (A.chart k (c ((A.chart j).symm z))))
    (star ∘ (fun w' => affCoord p (lift x₁ ((A.chart k).symm w'))) ∘ star)
    (fun y => affCoord p (lift x₀ ((A.chart j).symm y))) w ?_ ?_ hHa hFc ?_
  · rw [hFw]; exact analyticAt_star_comp hψ
  · rw [hFw]; exact ker_fderiv_star_comp hψ.differentiableAt hker
  · filter_upwards [e1, e2] with y h1 h2
    obtain ⟨h2s, h2u⟩ := h2
    generalize hy' : (A.chart j).symm y = y' at h1 h2s h2u
    have ho1 : SameOrbit (lift x₁ (c y')) (lift (c y') (c y')) := hCp _ _ _ ⟨h2u, hUm _⟩
    have ho2 : SameOrbit (lift y' y') (lift x₀ y') := hCp _ _ _ ⟨hUm _, h1⟩
    have ho : SameOrbit (lift x₁ (c y')) (cj (lift x₀ y')) :=
      sameOrbit_trans ho1 (sameOrbit_trans (hc y') (sameOrbit_cj ho2))
    have hst : (star : ((Σ k, ι k) → ℂ) → _) (cj (affCoord p (lift x₀ y'))) = affCoord p (lift x₀ y') := by
      funext q; simp [cj]
    simp only [Function.comp, star_star, hy', (A.chart k).left_inv h2s]
    rw [affCoord_eq_of_orbit p ho, affCoord_cj, hst]

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDimensionComplementEquiv
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Coord

theorem nat_card_cIdx (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (ca cb : Fin N) (hj : j ≤ N)
    (hab : ca < cb) (hblk : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) :
    Nat.card (FC.CIdx Ψ N j τ ca cb) + 1 = Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  classical
  obtain ⟨q0, hq0⟩ : ∃ q0 : LowIdx Ψ N j, q0.1 = (τ, cb, ca) := ⟨⟨(τ, cb, ca), hab, hblk⟩, rfl⟩
  have e : FC.CIdx Ψ N j τ ca cb ≃ {q : LowIdx Ψ N j // q ≠ q0} :=
    Equiv.subtypeEquivRight (fun q => by
      show q.1 ≠ (τ, cb, ca) ↔ q ≠ q0
      rw [← hq0]
      exact not_congr Subtype.ext_iff.symm)
  have h1 : Nat.card (Option {q : LowIdx Ψ N j // q ≠ q0}) = Nat.card (LowIdx Ψ N j) :=
    Nat.card_congr (Equiv.optionSubtypeNe q0)
  rw [Nat.card_eq_fintype_card, Fintype.card_option] at h1
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, h1, Nat.card_eq_fintype_card]
  convert GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.card_lowIdx Ψ N j hj

theorem nonempty_equiv_cIdx : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n d : ℕ) (τ : Ψ) (ca cb : Fin N), j ≤ N →
    ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) →
    d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) →
    Nonempty (Fin d ≃ Fin n ⊕ FC.CIdx Ψ N j τ ca cb) := by
  intro Ψ _ _ N j n d τ ca cb hj hab hblk hd
  have h := nat_card_cIdx Ψ N j τ ca cb hj hab hblk
  apply Finite.card_eq.1
  rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin d), Fintype.card_fin,
    Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
  omega

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Coord
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormProductFormulaStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_product_formula : ∀ (N : ℕ) (P : Fin N → Prop) (t : ℂ) (v f : Fin N → ℂ) (e : Fin N → ℤ), t ≠ 0 → (∀ i, ¬ P i → v i ≠ 0 ∧ f i ≠ 0) → Real.log ‖t * ∏ i : Fin N, (if P i then 1 else v i * f i) ^ e i‖ = Real.log ‖t‖ + ∑ i : Fin N, (e i : ℝ) * (if P i then 0 else Real.log ‖v i‖ + Real.log ‖f i‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_mul_prod_ite_zpow | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_mul_prod_ite_zpow | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_mul_prod_ite_zpow <;> assumption)
end

