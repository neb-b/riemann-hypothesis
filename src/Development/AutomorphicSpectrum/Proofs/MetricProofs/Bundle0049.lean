module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialBlockDecomposition
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodChartPotentialLeviForm
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticProjectionBijective
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem re_pi_bijective : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), Function.Bijective FA.Re.π := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA
  have hdeg0 := FA.Re.degree
  unfold ReciprocityTheory.AnForm.M.IsDegreeOff at hdeg0
  have hdeg := hdeg0.2.2.2.2.1
  rw [FA.br_empty, FA.deg_one] at hdeg
  have h1 : ∀ x, ∃ a, FA.Re.π ⁻¹' {x} = {a} := fun x => Set.ncard_eq_one.1 (hdeg x (by simp))
  constructor
  · intro a b hab
    obtain ⟨c, hc⟩ := h1 (FA.Re.π a)
    have ha : a ∈ FA.Re.π ⁻¹' {FA.Re.π a} := Set.mem_preimage.2 (Set.mem_singleton _)
    have hb : b ∈ FA.Re.π ⁻¹' {FA.Re.π a} := Set.mem_preimage.2 (Set.mem_singleton_iff.2 hab.symm)
    rw [hc] at ha hb
    exact (Set.mem_singleton_iff.1 ha).trans (Set.mem_singleton_iff.1 hb).symm
  · intro x
    obtain ⟨c, hc⟩ := h1 x
    have hcx : c ∈ FA.Re.π ⁻¹' {x} := by
      rw [hc]
      exact Set.mem_singleton c
    exact ⟨c, Set.mem_singleton_iff.1 (Set.mem_preimage.1 hcx)⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDimensionIndexEquiv
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount

theorem sum_range_eq_choose (m : ℕ) : ∑ i ∈ Finset.range m, i = m.choose 2 := by
  rw [Finset.sum_range_id, Nat.choose_two_right]

theorem card_row (N j : ℕ) (hj : j ≤ N) (a : Fin N) :
    Fintype.card {b : Fin N // b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} =
      if (a : ℕ) < N - j then (a : ℕ) else (a : ℕ) - (N - j) := by
  rw [Fintype.card_subtype]
  have key : (Finset.univ.filter fun b : Fin N => b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)).map
      Fin.valEmbedding = Finset.Ico (if (a : ℕ) < N - j then 0 else N - j) (a : ℕ) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨b, ⟨hba, hiff⟩, rfl⟩
      have hba' : (b : ℕ) < a := hba
      split_ifs with h
      · exact ⟨Nat.zero_le _, hba'⟩
      · exact ⟨Nat.le_of_not_lt (fun hb => h (hiff.mpr hb)), hba'⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨x, lt_trans h2 a.isLt⟩, ⟨h2, ?_⟩, rfl⟩
      show (a : ℕ) < N - j ↔ x < N - j
      split_ifs at h1 with h
      · exact ⟨fun _ => lt_trans h2 h, fun _ => h⟩
      · exact ⟨fun h' => absurd h' h, fun h' => absurd h1 (Nat.not_le.mpr h')⟩
  rw [← Finset.card_map Fin.valEmbedding, key, Nat.card_Ico]
  split_ifs <;> simp

theorem card_pairs (N j : ℕ) (hj : j ≤ N) :
    Fintype.card {p : Fin N × Fin N // p.2 < p.1 ∧ ((p.1 : ℕ) < N - j ↔ (p.2 : ℕ) < N - j)} =
      j.choose 2 + (N - j).choose 2 := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (a b : Fin N) => b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j))), Fintype.card_sigma]
  have h1 : ∀ a : Fin N, Fintype.card {b : Fin N // b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} =
      if (a : ℕ) < N - j then (a : ℕ) else (a : ℕ) - (N - j) := card_row N j hj
  simp only [h1]
  have hs : ∑ a : Fin N, (if (a : ℕ) < N - j then (a : ℕ) else (a : ℕ) - (N - j)) =
      ∑ i ∈ Finset.range N, (if i < N - j then i else i - (N - j)) :=
    Fin.sum_univ_eq_sum_range (fun i => if i < N - j then i else i - (N - j)) N
  rw [hs]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + j := ⟨N - j, by omega⟩
  have hM : M + j - j = M := by omega
  rw [hM, Finset.sum_range_add]
  have e1 : ∑ x ∈ Finset.range M, (if x < M then x else x - M) = ∑ x ∈ Finset.range M, x :=
    Finset.sum_congr rfl (fun x hx => if_pos (Finset.mem_range.mp hx))
  have e2 : ∑ x ∈ Finset.range j, (if M + x < M then M + x else M + x - M) =
      ∑ x ∈ Finset.range j, x :=
    Finset.sum_congr rfl (fun x _ => by rw [if_neg (by omega)]; omega)
  rw [e1, e2, sum_range_eq_choose, sum_range_eq_choose, add_comm]

theorem card_lowIdx (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hj : j ≤ N) :
    Fintype.card (LowIdx Ψ N j) = Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  rw [← card_pairs N j hj, ← Fintype.card_prod]
  exact Fintype.card_congr
    { toFun := fun q => (q.1.1, ⟨q.1.2, q.2⟩)
      invFun := fun x => ⟨(x.1, x.2.1), x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem nonempty_paramEquiv : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n d : ℕ), j ≤ N →
    d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) →
    Nonempty (Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)) := by
  intro Ψ _ _ N j n d hj hd
  apply Fintype.card_eq.mp
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, card_lowIdx Ψ N j hj,
    Fintype.card_unit, Fintype.card_fin]
  generalize Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) = t at hd ⊢
  omega

end GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackFirst
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CWeight

section Calc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}

def SmMat (M : E → Matrix (Fin N) (Fin N) ℂ) (w : E) : Prop :=
  ∀ a b, ContDiffAt ℝ ∞ (fun u => M u a b) w

theorem SmMat.mul {M M' : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : SmMat M w) (h' : SmMat M' w) :
    SmMat (fun u => M u * M' u) w := by
  intro a b
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun c _ => (h a c).mul (h' c b)

theorem SmMat.conjTranspose {M : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : SmMat M w) :
    SmMat (fun u => (M u)ᴴ) w := by
  intro a b
  simp only [Matrix.conjTranspose_apply]
  exact (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.contDiffAt.comp w (h b a)

theorem SmMat.minor {M : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : SmMat M w) (I J : Finset (Fin N)) :
    ContDiffAt ℝ ∞ (fun u => minorIJ (M u) I J) w := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e, Matrix.det_apply']
    refine ContDiffAt.sum fun σ _ => contDiffAt_const.mul ?_
    exact contDiffAt_prod fun i _ => h _ _
  · simp only [dif_neg e]
    exact contDiffAt_const

theorem contDiffAt_blockPot (j : ℕ) (i : Fin N) {G h : E → Matrix (Fin N) (Fin N) ℂ} {w : E}
    (hG : SmMat G w) (hh : SmMat h w) (hpos : (G w).PosDef) (hdet : (h w).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun u => blockPot j i (G u) (h u)) w := by
  have hre : ∀ {f : E → ℂ}, ContDiffAt ℝ ∞ f w → 0 < f w →
      ContDiffAt ℝ ∞ (fun u => Real.log (f u).re) w := fun hf h0 =>
    (Complex.reCLM.contDiff.contDiffAt.comp w hf).log (Complex.lt_def.1 h0).1.ne'
  have hfac : ContDiffAt ℝ ∞ (fun u => detFac j i (G u)) w := by
    unfold detFac
    refine ContDiffAt.mul ?_ ?_
    · by_cases c : j ≤ (i : ℕ) + 1
      · simpa only [if_pos c] using hG.minor _ _
      · simpa only [if_neg c] using contDiffAt_const
    · by_cases c : (i : ℕ) + 1 = N
      · simpa only [if_pos c] using hG.minor _ _
      · simpa only [if_neg c] using contDiffAt_const
  have hfac0 : 0 < detFac j i (G w) := by
    unfold detFac
    refine mul_pos ?_ ?_
    · split_ifs
      · exact GramPot.minor_pos hpos _
      · exact zero_lt_one
    · split_ifs
      · exact GramPot.minor_pos hpos _
      · exact zero_lt_one
  unfold blockPot
  refine (contDiffAt_const.mul (hre hfac hfac0)).add ?_
  by_cases c : IsProperStep N j i
  · simp only [if_pos c]
    refine contDiffAt_const.mul (hre ((hh.conjTranspose.mul hG).mul hh |>.minor _ _) ?_)
    have hu : IsUnit (h w) := (Matrix.isUnit_iff_isUnit_det _).2 hdet.isUnit
    exact GramPot.minor_pos
      (hpos.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)) _
  · simp only [if_neg c]
    exact contDiffAt_const

end Calc

section Chart

variable {e n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem contDiffAt_comp_holoMap {A : FinHolAtlas e X} {B : FinHolAtlas n Y} {pr : X → Y}
    (hp : HoloMap A B pr) {U : Set Y} (hU : IsOpen U) {f : Y → ℝ} (hf : B.SmoothOn U f)
    (c : Fin A.n) {w : Fin e → ℂ} (hw : w ∈ (A.chart c).target)
    (hwU : pr ((A.chart c).symm w) ∈ U) :
    ContDiffAt ℝ ∞ (fun u => f (pr ((A.chart c).symm u))) w := by
  obtain ⟨k, hk⟩ := B.cover (pr ((A.chart c).symm w))
  have h1 : ContDiffAt ℝ ∞ (f ∘ (B.chart k).symm) (B.chart k (pr ((A.chart c).symm w))) := by
    refine (hf k).contDiffAt
      (((B.chart k).isOpen_inter_preimage_symm hU).mem_nhds ⟨(B.chart k).map_source hk, ?_⟩)
    simpa [(B.chart k).left_inv hk] using hwU
  have h2 : ContDiffAt ℝ ∞ (B.chart k ∘ pr ∘ (A.chart c).symm) w :=
    (hp.2 c k w ⟨hw, hk⟩).contDiffAt.restrict_scalars ℝ
  refine (ContDiffAt.comp w h1 h2).congr_of_eventuallyEq ?_
  filter_upwards [((A.chart c).isOpen_inter_preimage_symm
    ((B.chart k).open_source.preimage hp.1)).mem_nhds ⟨hw, hk⟩] with u hu
  simp only [Function.comp_apply, (B.chart k).left_inv hu.2]

theorem contDiffAt_of_re_im {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℂ} {w : E}
    (h1 : ContDiffAt ℝ ∞ (fun u => (g u).re) w) (h2 : ContDiffAt ℝ ∞ (fun u => (g u).im) w) :
    ContDiffAt ℝ ∞ g w := by
  have e : g = fun u => (((g u).re : ℝ) : ℂ) + (((g u).im : ℝ) : ℂ) * Complex.I := by
    funext u
    exact (Complex.re_add_im _).symm
  rw [e]
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp w h1).add
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp w h2).mul contDiffAt_const)

end Chart

theorem smoothOn_stepPh : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → R.A.SmoothOn (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (stepPh M BM p v R pr) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hS hP c w hw
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨hwt, hwb⟩ := hw
  have hb : pr ((R.A.chart c).symm w) ∉ bdry BM.s := hwb
  obtain ⟨W, l, H, D, hWo, hyW, hWU, hWO, hH, hHd, hD, hD0, heq⟩ :=
    hS ((R.A.chart c).symm w) ((R.A.chart c).symm w) (R.mem_U _)
  have hcl : IsClosed (bdry BM.s) := isClosed_bdry_of_isSection _ _ _ _ _ BM.sec
  have hOo : IsOpen (W ∩ pr ⁻¹' (bdry BM.s)ᶜ) := hWo.inter (hcl.isOpen_compl.preimage hp.1)
  have hnhd : (R.A.chart c).target ∩ (R.A.chart c).symm ⁻¹' (W ∩ pr ⁻¹' (bdry BM.s)ᶜ) ∈ 𝓝 w :=
    ((R.A.chart c).isOpen_inter_preimage_symm hOo).mem_nhds ⟨hwt, hyW, hb⟩
  have hOb : IsOpen (BM.O l \ bdry BM.s) := (BM.O_open l).sdiff hcl
  have hmemO : pr ((R.A.chart c).symm w) ∈ BM.O l \ bdry BM.s := ⟨hWO _ hyW, hb⟩
  have hG : SmMat (fun u => BM.G l p.1 (pr ((R.A.chart c).symm u))) w := fun a b =>
    contDiffAt_of_re_im
      (contDiffAt_comp_holoMap hp hOb (BM.G_smooth l p.1 a b).1 c hwt hmemO)
      (contDiffAt_comp_holoMap hp hOb (BM.G_smooth l p.1 a b).2 c hwt hmemO)
  have hHm : SmMat (fun u => H ((R.A.chart c).symm u)) w := fun a b =>
    (hH a b c w ⟨hwt, hyW⟩).contDiffAt.restrict_scalars ℝ
  have hDm : ContDiffAt ℝ ∞ (fun u => D ((R.A.chart c).symm u)) w :=
    (hD c w ⟨hwt, hyW⟩).contDiffAt.restrict_scalars ℝ
  have hD1 : D ((R.A.chart c).symm w) ≠ 0 := hD0 _ hyW
  have hbp := contDiffAt_blockPot j p.2 hG hHm (BM.G_pos l p.1 _ hmemO).2 (hHd _ hyW).2
  have hlog : ContDiffAt ℝ ∞ (fun u => Real.log ‖D ((R.A.chart c).symm u)‖) w :=
    (hDm.norm ℝ hD1).log (norm_ne_zero_iff.2 hD1)
  have hpot : ContDiffAt ℝ ∞ (fun u => Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h
      (R.lift ((R.A.chart c).symm w) ((R.A.chart c).symm u)))) w :=
    (hP.1 ((R.A.chart c).symm w) c).contDiffAt
      (((R.A.chart c).isOpen_inter_preimage_symm (R.isOpen_U _)).mem_nhds ⟨hwt, R.mem_U _⟩)
  refine ((hbp.add hlog).sub hpot).congr_of_eventuallyEq ?_
  filter_upwards [hnhd] with u hu
  have := heq _ hu.2.1 hu.2.2
  simp only [Function.comp_apply]
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.CWeight
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackSecond
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

section Holo

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem continuousOn_of_holoOn {V : Set X} (hV : IsOpen V) {g : X → ℂ} (h : A.HoloOn V g) :
    ContinuousOn g V := by
  intro y hy
  obtain ⟨k, hk⟩ := A.cover y
  have hz : A.chart k y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V :=
    ⟨(A.chart k).map_source hk, by
      show (A.chart k).symm (A.chart k y) ∈ V
      rw [(A.chart k).left_inv hk]; exact hy⟩
  have h1 : ContinuousAt (g ∘ (A.chart k).symm) (A.chart k y) := (h k _ hz).continuousAt
  have h2 : ContinuousAt (A.chart k) y := (A.chart k).continuousAt hk
  have h3 : ContinuousAt ((g ∘ (A.chart k).symm) ∘ (A.chart k)) y := ContinuousAt.comp h1 h2
  refine (h3.congr ?_).continuousWithinAt
  filter_upwards [(A.chart k).open_source.mem_nhds hk] with u hu
  simp [(A.chart k).left_inv hu]

theorem holoOn_comp {e' : ℕ} {Y : Type} [TopologicalSpace Y] {B : FinHolAtlas e' Y} {h : Y → X}
    (hh : HoloMap B A h) {V : Set X} {g : X → ℂ} (hg : A.HoloOn V g) :
    B.HoloOn (h ⁻¹' V) fun y => g (h y) := by
  intro c z hz
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart c).symm z))
  have h1 : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart c).symm) z := hh.2 c k z ⟨hz.1, hk⟩
  have h2 : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (B.chart c).symm) z) :=
    hg k _ ⟨(A.chart k).map_source hk, by
      show (A.chart k).symm (A.chart k (h ((B.chart c).symm z))) ∈ V
      rw [(A.chart k).left_inv hk]; exact hz.2⟩
  refine (h2.comp h1).congr ?_
  have hc : ContinuousAt (h ∘ (B.chart c).symm) z :=
    hh.1.continuousAt.comp ((B.chart c).continuousAt_symm hz.1)
  filter_upwards [hc.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)] with u hu
  have hu' : h ((B.chart c).symm u) ∈ (A.chart k).source := hu
  simp only [Function.comp]
  rw [(A.chart k).left_inv hu']

theorem holoOn_mono {U V : Set X} {g : X → ℂ} (h : A.HoloOn U g) (hVU : V ⊆ U) : A.HoloOn V g :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))

theorem holoOn_mul {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U fun x => f x * g x :=
  fun j z hz => (hf j z hz).mul (hg j z hz)

theorem holoOn_const (V : Set X) (c : ℂ) : A.HoloOn V fun _ => c := fun _ _ _ => analyticAt_const

theorem holoOn_sum {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∑ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_sum s fun a _ => h a k z hz

theorem holoOn_prod {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∏ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_prod s fun a _ => h a k z hz

theorem holoOn_inv {V : Set X} {f : X → ℂ} (h : A.HoloOn V f) (h0 : ∀ y ∈ V, f y ≠ 0) :
    A.HoloOn V fun y => (f y)⁻¹ := fun k z hz => (h k z hz).inv (h0 _ hz.2)

theorem holoOn_det {σ : Type} [Fintype σ] [DecidableEq σ] {V : Set X} {m : X → Matrix σ σ ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) : A.HoloOn V fun y => (m y).det := by
  simp only [Matrix.det_apply']
  exact holoOn_sum _ fun s => holoOn_mul (holoOn_const _ _) (holoOn_prod _ fun a => h _ _)

theorem holoOn_minorIJ {N : ℕ} {V : Set X} {m : X → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) (I J : Finset (Fin N)) :
    A.HoloOn V fun y => minorIJ (m y) I J := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e]
    exact holoOn_det fun a b => h _ _
  · simp only [dif_neg e]
    exact holoOn_const _ _

theorem holoOn_detFac {N j : ℕ} (i : Fin N) {V : Set X} {m : X → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) : A.HoloOn V fun y => detFac j i (m y) := by
  unfold detFac
  refine holoOn_mul ?_ ?_
  · split_ifs
    · exact holoOn_minorIJ h _ _
    · exact holoOn_const _ _
  · split_ifs
    · exact holoOn_minorIJ h _ _
    · exact holoOn_const _ _

theorem exists_log {S : Set X} (hS : IsOpen S) {f : X → ℂ} (h : A.HoloOn S f) {y : X} (hy : y ∈ S)
    (h0 : f y ≠ 0) : ∃ W', IsOpen W' ∧ y ∈ W' ∧ W' ⊆ S ∧ ∃ G : X → ℂ, A.HoloOn W' G ∧
      ∀ z ∈ W', (G z).re = Real.log ‖f z‖ := by
  refine ⟨S ∩ (fun z => f z * (f y)⁻¹) ⁻¹' Complex.slitPlane,
    ((continuousOn_of_holoOn hS h).mul continuousOn_const).isOpen_inter_preimage hS Complex.isOpen_slitPlane,
    ⟨hy, ?_⟩, Set.inter_subset_left, fun z => Complex.log (f z * (f y)⁻¹) + Real.log ‖f y‖,
    fun k u hu => ?_, fun z hz => ?_⟩
  · simp [mul_inv_cancel₀ h0]
  · exact (AnalyticAt.clog ((h k u ⟨hu.1, hu.2.1⟩).mul analyticAt_const) hu.2.2).add analyticAt_const
  · have hz0 : f z ≠ 0 := left_ne_zero_of_mul (Complex.slitPlane_ne_zero hz.2)
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, ← div_eq_mul_inv, norm_div,
      Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 h0), sub_add_cancel]

end Holo

theorem minorIJ_one_self {N : ℕ} (I : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I I = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem detFac_ne_zero' {N j : ℕ} (hj : j ≤ N) (i : Fin N) {H : Matrix (Fin N) (Fin N) ℂ}
    (hb : IsBlockDiag j H) (hd : H.det ≠ 0) : detFac j i H ≠ 0 := by
  have hu : IsUnit H.det := hd.isUnit
  have h1 := ((_root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j i hj).2.2.2 H H⁻¹ hb (hb.inv hu)).2
  rw [Matrix.mul_nonsing_inv _ hu] at h1
  have h2 : detFac j i (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    unfold detFac
    split_ifs <;> simp [minorIJ_one_self]
  intro h0
  rw [h2, h0, zero_mul] at h1
  exact one_ne_zero h1

theorem isPshOn_stepPot : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPshOn R.A (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun (stepPh M BM p v R pr)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hS x c y₀ hy w
  obtain ⟨hyt, hyU, hyb⟩ := hy
  have hU : (R.A.chart c).symm y₀ ∈ R.U x := hyU.1
  set y₁ := (R.A.chart c).symm y₀ with hy₁
  obtain ⟨W, l, H, D, hW, hyW, hWU, hWO, hHh, hHd, hDh, hDn, hEq⟩ := hS x y₁ hU
  have hb : pr y₁ ∉ bdry BM.s := hyb
  obtain ⟨V, Pi, hV, hVo, hPh, hPg⟩ := BM.period l (pr y₁) ⟨hWO y₁ hyW, hb⟩
  have hcl : IsClosed (bdry BM.s) := _root_.GlobalTheory.CompanionTheory.Ar.PB.CWeight.isClosed_bdry_of_isSection _ _ _ _ _ BM.sec
  let V' : Set R.X := W ∩ pr ⁻¹' (V ∩ (bdry BM.s)ᶜ)
  have hV'o : IsOpen V' := hW.inter ((hVo.inter hcl.isOpen_compl).preimage hp.1)
  have hyV' : y₁ ∈ V' := ⟨hyW, hV, hb⟩
  let g : R.X → Matrix (Fin N) (Fin N) ℂ := fun y' => Pi p.1 (pr y') * H y'
  have hVW : V' ⊆ W := Set.inter_subset_left
  have hVP : V' ⊆ pr ⁻¹' V := fun y' h => h.2.1
  have hPh' : ∀ a b, R.A.HoloOn V' fun y' => Pi p.1 (pr y') a b := fun a b =>
    holoOn_mono (holoOn_comp hp (hPh p.1 a b)) hVP
  have hHh' : ∀ a b, R.A.HoloOn V' fun y' => H y' a b := fun a b =>
    holoOn_mono (hHh a b) hVW
  have hgh : ∀ a b, R.A.HoloOn V' fun y' => g y' a b := fun a b => by
    simp only [g, Matrix.mul_apply]
    exact holoOn_sum _ fun c' => holoOn_mul (hPh' a c') (hHh' c' b)
  have hstep : ∀ (i : Fin N), ∀ y' ∈ V', InFlagDomain N j (g y') ∧
      stepPot N j i (g y') = blockPot j i (BM.G l p.1 (pr y')) (H y') + Real.log ‖detFac j i (H y')‖ := by
    intro i y' hy'
    have hG := BM.G_pos l p.1 (pr y') ⟨hWO y' hy'.1, hy'.2.2⟩
    exact _root_.GlobalTheory.CompanionTheory.Ar.PB.stepPot_mul_eq_blockPot N j i _ _ _ M.j_le (hPg p.1 _ hy'.2.1) hG.1 hG.2 (hHd y' hy'.1).1 (hHd y' hy'.1).2
  have hdn : ∀ y' ∈ V', detFac j p.2 (H y') ≠ 0 := fun y' hy' =>
    detFac_ne_zero' M.j_le p.2 (hHd y' hy'.1).1 (hHd y' hy'.1).2
  let f : R.X → ℂ := fun y' => D y' * (detFac j p.2 (H y'))⁻¹
  have hfh : R.A.HoloOn V' f :=
    holoOn_mul (holoOn_mono hDh hVW) (holoOn_inv (holoOn_detFac p.2 hHh') hdn)
  have hf0 : ∀ y' ∈ V', f y' ≠ 0 := fun y' hy' =>
    mul_ne_zero (hDn y' hy'.1) (inv_ne_zero (hdn y' hy'))
  obtain ⟨V'', hV''o, hyV'', hV''s, Gh, hGh, hGre⟩ := exists_log hV'o hfh hyV' (hf0 _ hyV')
  let Φl : R.X → ℝ := (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun (stepPh M BM p v R pr)).φ x
  let pot : Unit × Fin N → LocPot R.X := fun q =>
    LocPot.ofFun (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y'))
  have hPC : IsPeriodChart R.A j pot y₁ V'' (fun _ => g) := by
    refine ⟨hV''o, hyV'', fun _ a b => holoOn_mono (hgh a b) hV''s,
      fun _ y' hy' => (hstep p.2 y' (hV''s hy')).1, fun q => ?_⟩
    by_cases hq : q.2 = p.2
    · refine ⟨Gh, hGh, fun y' hy' => ?_⟩
      have hy3 := hV''s hy'
      show (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y')) y' = stepPot N j q.2 (g y') + (Gh y').re
      rw [if_pos hq, hq, hGre y' hy', (hstep p.2 y' hy3).2]
      have hE := hEq y' hy3.1 hy3.2.2
      have hl : Real.log ‖f y'‖ = Real.log ‖D y'‖ - Real.log ‖detFac j p.2 (H y')‖ := by
        simp only [f]
        rw [norm_mul, norm_inv, Real.log_mul (norm_ne_zero_iff.2 (hDn y' hy3.1))
          (inv_ne_zero (norm_ne_zero_iff.2 (hdn y' hy3))), Real.log_inv, sub_eq_add_neg]
      rw [hl]
      show Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift x y')) + stepPh M BM p v R pr y' = _
      rw [hE]
      ring
    · refine ⟨fun _ => 0, holoOn_const _ _, fun y' _ => ?_⟩
      show (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y')) y' = stepPot N j q.2 (g y') + ((0 : ℂ)).re
      rw [if_neg hq]
      simp
  have hsrc : y₁ ∈ (R.A.chart c).source := (R.A.chart c).map_target hyt
  obtain ⟨Lm, -, hL, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.levi_diagonal_of_isPeriodChart e R.X R.A Unit N j M.j_le pot y₁ V'' (fun _ => g) hPC c hsrc
  have hlev := hL ((), p.2) w
  have e1 : (R.A.chart c) y₁ = y₀ := (R.A.chart c).right_inv hyt
  have e2 : (pot ((), p.2)).φ y₁ = Φl := by
    show (if p.2 = p.2 then Φl else fun y' => stepPot N j p.2 (g y')) = Φl
    rw [if_pos rfl]
  rw [e2, e1] at hlev
  show 0 ≤ levi (Φl ∘ (R.A.chart c).symm) y₀ w
  rw [hlev]
  refine Finset.sum_nonneg fun q _ => ?_
  split_ifs
  · positivity
  · exact le_rfl

end GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW
end
end

