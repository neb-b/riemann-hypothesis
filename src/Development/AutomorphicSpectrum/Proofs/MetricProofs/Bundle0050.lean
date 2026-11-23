module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFlModel
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackThird
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize

theorem continuousAt_of_chart {X E F : Type*} [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace F]
    (c : OpenPartialHomeomorph X E) {f : X → F} {x : X} (hx : x ∈ c.source)
    (h : ContinuousAt (f ∘ c.symm) (c x)) : ContinuousAt f x := by
  have h1 : ContinuousAt ((f ∘ c.symm) ∘ c) x := ContinuousAt.comp h (c.continuousAt hx)
  refine h1.congr ?_
  filter_upwards [c.open_source.mem_nhds hx] with z hz
  simp [c.left_inv hz]

theorem holoOn_continuousAt {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X) {W : Set X}
    {g : X → ℂ} (h : A.HoloOn W g) {x : X} (hx : x ∈ W) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  refine continuousAt_of_chart (A.chart j) hj ?_
  have hm : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  exact (h j _ hm).continuousAt

theorem smoothOn_continuousAt {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X) {W : Set X}
    (hW : IsOpen W) {g : X → ℝ} (h : A.SmoothOn W g) {x : X} (hx : x ∈ W) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  refine continuousAt_of_chart (A.chart j) hj ?_
  have hm : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
    (A.chart j).isOpen_inter_preimage_symm hW
  exact ((h j).continuousOn).continuousAt (ho.mem_nhds hm)

variable {N : ℕ}

theorem gram_cmp {k : ℕ} (hk : k ≤ N) {G : Matrix (Fin N) (Fin N) ℂ} (V : Matrix (Fin N) (Fin k) ℂ) {m : ℝ}
    (hm : 1 ≤ m) (hG : G.PosDef) (h1 : ((m : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef)
    (h2 : ((m : ℂ) • G - 1).PosSemidef) (hV : LinearIndependent ℂ Vᵀ) :
    |Real.log (Vᴴ * G * V).det.re - Real.log (Vᴴ * (1 : Matrix (Fin N) (Fin N) ℂ) * V).det.re| ≤ N * Real.log m := by
  refine (_root_.GlobalTheory.CompanionTheory.Ar.PB.gram_det_log_size N k G 1 V m hm Matrix.PosDef.one hG h1 h2 hV).trans ?_
  have : (k : ℝ) ≤ N := by exact_mod_cast hk
  exact mul_le_mul_of_nonneg_right this (Real.log_nonneg hm)

theorem card_le (S : Finset (Fin N)) : S.card ≤ N := by
  simpa using S.card_le_univ

theorem blockPot_sub_le (j : ℕ) (i : Fin N) {G h : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (hd : h.det ≠ 0)
    {m : ℝ} (hm : 1 ≤ m) (h1 : ((m : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef)
    (h2 : ((m : ℂ) • G - 1).PosSemidef) :
    |blockPot j i G h - blockPot j i 1 h| ≤ (3 / 2) * N * Real.log m := by
  obtain ⟨hS, hHS, hP⟩ := GramPot.blockPot_eq_gram N j i G h
  obtain ⟨-, -, hP1⟩ := GramPot.blockPot_eq_gram N j i 1 h
  have e1 := hP hG
  have e2 := hP1 Matrix.PosDef.one
  have tW := abs_le.1 (gram_cmp (card_le (wIdx N j)) (selM (wIdx N j)) hm hG h1 h2 (hS _))
  have tO := abs_le.1 (gram_cmp (card_le (omIdx N j)) (selM (omIdx N j)) hm hG h1 h2 (hS _))
  have tH := abs_le.1 (gram_cmp (card_le (stepCols N j i)) (h * selM (stepCols N j i)) hm hG h1 h2 (hHS hd _))
  have hl : 0 ≤ (N : ℝ) * Real.log m := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hm)
  rw [e1, e2, abs_le]
  split_ifs <;> constructor <;> linarith [tW.1, tW.2, tO.1, tO.2, tH.1, tH.2]

theorem size_abs {G : Matrix (Fin N) (Fin N) ℂ} {r c : ℝ} (hr : 1 ≤ r) (hG : G.PosDef)
    (h : (((r ^ c : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef ∧
      (((r ^ c : ℝ) : ℂ) • G - 1).PosSemidef) :
    (((r ^ |c| : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef ∧
      (((r ^ |c| : ℝ) : ℂ) • G - 1).PosSemidef := by
  have hd : (0 : ℝ) ≤ r ^ |c| - r ^ c := sub_nonneg.2 (Real.rpow_le_rpow_of_exponent_le hr (le_abs_self c))
  have hd' : (0 : ℂ) ≤ ((r ^ |c| - r ^ c : ℝ) : ℂ) := by exact_mod_cast hd
  constructor
  · have := h.1.add (Matrix.PosSemidef.one.smul hd')
    convert this using 1
    push_cast
    module
  · have := h.2.add (hG.posSemidef.smul hd')
    convert this using 1
    push_cast
    module

theorem gram_one_pos {h : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) (S : Finset (Fin N)) :
    0 < (minorIJ (hᴴ * 1 * h) S S).re := by
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 hd.isUnit
  have hp : (hᴴ * 1 * h).PosDef :=
    Matrix.PosDef.one.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
  exact (Complex.lt_def.1 (GramPot.minor_pos hp S)).1

theorem continuous_gram (S : Finset (Fin N)) :
    Continuous fun h : Matrix (Fin N) (Fin N) ℂ => (minorIJ (hᴴ * 1 * h) S S).re := by
  simp only [minorIJ, dif_pos]
  refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
  refine Continuous.matrix_submatrix ?_ _ _
  fun_prop

theorem continuousAt_blockPot_one {X : Type*} [TopologicalSpace X] (j : ℕ) (i : Fin N)
    {H : X → Matrix (Fin N) (Fin N) ℂ} {x : X} (hH : ∀ a b, ContinuousAt (fun y => H y a b) x)
    (hd : (H x).det ≠ 0) : ContinuousAt (fun y => blockPot j i 1 (H y)) x := by
  have hc : ContinuousAt H x :=
    continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => hH a b
  unfold blockPot
  refine continuousAt_const.add ?_
  split_ifs
  · refine continuousAt_const.mul (ContinuousAt.log ((continuous_gram _).continuousAt.comp hc) ?_)
    exact (gram_one_pos hd _).ne'
  · exact continuousAt_const

theorem stepPh_le_log : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → ∃ C₁ : ℝ, ∀ x ∉ bdry (fun x y => BM.s (pr x) (pr y)), |stepPh M BM p v R pr x| ≤ C₁ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hch hpot
  have hr : ∀ x, Real.exp 1 ≤ rW BM.L BM.s x := fun x => by
    have := BM.norm_le x
    simp only [rW]
    linarith
  have hrpos : ∀ x, 0 < rW BM.L BM.s x := fun x => (Real.exp_pos 1).trans_le (hr x)
  have hr1 : ∀ x, 1 ≤ rW BM.L BM.s x := fun x =>
    (by linarith [Real.add_one_le_exp (1 : ℝ)] : (1 : ℝ) ≤ Real.exp 1).trans (hr x)
  have hlog : ∀ x, 1 ≤ Real.log (rW BM.L BM.s x) := fun x =>
    (Real.le_log_iff_exp_le (hrpos x)).2 (hr x)
  have key : ∀ y₀ : R.X, ∃ t ∈ 𝓝 y₀, ∃ C : ℝ, ∀ x ∈ t, x ∉ bdry (fun x y => BM.s (pr x) (pr y)) →
      |stepPh M BM p v R pr x| ≤ C * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
    intro y₀
    obtain ⟨W, l, H, D, hW, hy₀, -, hO, hH, hHd, hD, hDne, heq⟩ := hch y₀ y₀ (R.mem_U y₀)
    let u : R.X → ℝ := fun y' => blockPot j p.2 1 (H y') + Real.log ‖D y'‖ -
      Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift y₀ y'))
    have hu : ContinuousAt u y₀ := by
      refine ((continuousAt_blockPot_one j p.2 (fun a b => holoOn_continuousAt R.A (hH a b) hy₀)
        (hHd y₀ hy₀).2).add ?_).sub ?_
      · exact ContinuousAt.log (holoOn_continuousAt R.A hD hy₀).norm (norm_ne_zero_iff.2 (hDne y₀ hy₀))
      · exact smoothOn_continuousAt R.A (R.isOpen_U y₀) (hpot.1 y₀) (R.mem_U y₀)
    refine ⟨W ∩ {y' | |u y'| < |u y₀| + 1}, inter_mem (hW.mem_nhds hy₀)
      (hu.abs.eventually_lt continuousAt_const (lt_add_one _)), (3 / 2) * N * |BM.Cst| + (|u y₀| + 1), ?_⟩
    rintro y' ⟨hy'W, hy'u⟩ hb
    have hb' : pr y' ∉ bdry BM.s := hb
    have hmem : pr y' ∈ BM.O l \ bdry BM.s := ⟨hO y' hy'W, hb'⟩
    obtain ⟨-, hpd⟩ := BM.G_pos l p.1 _ hmem
    have hs := size_abs (hr1 (pr y')) hpd (BM.size l p.1 _ hmem)
    have hm1 : 1 ≤ rW BM.L BM.s (pr y') ^ |BM.Cst| := Real.one_le_rpow (hr1 _) (abs_nonneg _)
    have hdiff := blockPot_sub_le j p.2 hpd (hHd y' hy'W).2 hm1 hs.1 hs.2
    rw [Real.log_rpow (hrpos _)] at hdiff
    have e' := heq y' hy'W hb'
    have hL := hlog (pr y')
    have hsum : stepPh M BM p v R pr y' = (blockPot j p.2 (BM.G l p.1 (pr y')) (H y') - blockPot j p.2 1 (H y')) + u y' := by
      simp only [u]
      linarith
    change |stepPh M BM p v R pr y'| ≤ _ * Real.log (rW BM.L BM.s (pr y'))
    rw [hsum]
    have hu' : |u y'| < |u y₀| + 1 := hy'u
    have hc : |u y₀| + 1 ≤ (|u y₀| + 1) * Real.log (rW BM.L BM.s (pr y')) :=
      le_mul_of_one_le_right (by positivity) hL
    calc _ ≤ |blockPot j p.2 (BM.G l p.1 (pr y')) (H y') - blockPot j p.2 1 (H y')| + |u y'| := abs_add_le _ _
      _ ≤ (3 / 2) * N * (|BM.Cst| * Real.log (rW BM.L BM.s (pr y'))) + (|u y₀| + 1) * Real.log (rW BM.L BM.s (pr y')) := by
        linarith
      _ = _ := by ring
  have hlogr : ∀ x, 0 ≤ Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := fun x =>
    zero_le_one.trans (hlog (pr x))
  obtain ⟨C, hC⟩ := (isCompact_univ (X := R.X)).induction_on
    (p := fun S => ∃ C : ℝ, ∀ x ∈ S, x ∉ bdry (fun x y => BM.s (pr x) (pr y)) →
      |stepPh M BM p v R pr x| ≤ C * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x))
    ⟨0, fun x hx => absurd hx (Set.notMem_empty x)⟩
    (fun s t hst ⟨C, hC⟩ => ⟨C, fun x hx => hC x (hst hx)⟩)
    (fun s t ⟨C, hC⟩ ⟨C', hC'⟩ => ⟨max C C', fun x hx hb => hx.elim
      (fun h => (hC x h hb).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlogr x)))
      (fun h => (hC' x h hb).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hlogr x)))⟩)
    (fun y₀ _ => by
      obtain ⟨t, ht, C, hC⟩ := key y₀
      exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, C, hC⟩)
  exact ⟨C, fun x hb => hC x (Set.mem_univ x) hb⟩

end GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyModelBaseMetric
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem flagModel_over_point : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → ∃ (M : FlagModel (yFl Ψ N) Ψ N N) (BM : BaseMetric M 0), (∀ p, BM.hom p = yLineFl Ψ N p) ∧ (∀ p, fsHerm (FlIdx Ψ N) (M.dy p) = yLineFl Ψ N p) ∧ bdry BM.s = ∅ := by
  exact @PositivityTheory.Xgp.t_c_fl_model

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericFlagElementaryTwist
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CPts.GenData

theorem gen_data : ∀ (Ω Φ : Type) [Field Ω] [Field Φ] [Algebra Ω Φ] (Ψ : Type) (N j : ℕ) (g : Ψ → Matrix (Fin N) (Fin N) Φ) (T : Ψ → Matrix (Fin N) (Fin N) Ω) (A : Subring Ω) (val : A →+* ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (τ : Ψ) (ca cb : Fin N), (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → (∀ τ, IsBlockDiag j (g τ)) → IsGenericFlag Ω j g → (∀ τ, IsBlockDiag j (T τ) ∧ (T τ).det ≠ 0) → (∀ τ, IsBlockDiag j (h τ)) → ∃ (L R : Type) (_ : Field L) (_ : CommRing R) (φ : Φ →+* L) (θ : RatFunc Φ →+* L) (U : Ψ → Matrix (Fin N) (Fin N) L) (s : L) (i : R →+* L) (ρ : R →+* ℂ) (cA : A →+* R) (B : Ψ → Matrix (Fin N) (Fin N) R) (sR : R), Function.Injective i ∧ (∀ a, θ (algebraMap Φ (RatFunc Φ) a) = φ a) ∧ (∀ τ', IsBlockDiag j (U τ') ∧ (U τ').BlockTriangular id ∧ ∀ c, U τ' c c ≠ 0) ∧ U τ ca ca + s * U τ ca cb ≠ 0 ∧ θ RatFunc.X * (U τ ca ca + s * U τ ca cb) = s * U τ cb cb ∧ (∀ a : A, i (cA a) = φ (algebraMap Ω Φ a)) ∧ (∀ a, ρ (cA a) = val a) ∧ (∀ τ', IsBlockDiag j (B τ')) ∧ (∀ τ', (B τ').map i = ((T τ')⁻¹.map (φ.comp (algebraMap Ω Φ))) * ((g τ').map φ * U τ')) ∧ (∀ τ', (B τ').map ρ = h τ') ∧ i sR = s ∧ ρ sR = t := by
  intro Ω Φ _ _ _ Ψ N j g T A val h t τ ca cb hcb hsum hgb hgen hT hh
  let S₀ := MvPolynomial (UpIdx Ψ N j) Φ
  let P := Polynomial S₀
  let L := FractionRing P
  let Q := MvPolynomial (inertBlockIndex Ψ N j) A
  let R := Polynomial Q
  let aL : P →+* L := algebraMap P L
  let cP : S₀ →+* P := Polynomial.C
  let φ : Φ →+* L := aL.comp (cP.comp (C : Φ →+* S₀))
  let U : Ψ → Matrix (Fin N) (Fin N) L := fun τ' => (genUp Φ N j τ').map (aL.comp cP)
  let s : L := aL Polynomial.X
  let G' : Ψ → Matrix (Fin N) (Fin N) S₀ := fun τ' =>
    ((T τ')⁻¹.map (algebraMap Ω S₀)) * ((g τ').map (C : Φ →+* S₀) * genUp Φ N j τ')
  have indep := @GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag.indep_twist_mul_genUp Ω Φ _ _ _ Ψ N j g T hgb hgen hT
  let iS : Q →+* S₀ := eval₂Hom ((algebraMap Ω S₀).comp A.subtype) fun q => G' q.1.1 q.1.2.1 q.1.2.2
  have iS_C : ∀ a : A, iS (C a) = algebraMap Ω S₀ a := fun a => eval₂Hom_C _ _ _
  have iS_X : ∀ q, iS (X q) = G' q.1.1 q.1.2.1 q.1.2.2 := fun q => eval₂Hom_X' _ _ _
  have eS : ∀ r, iS r = aeval (fun q : inertBlockIndex Ψ N j => G' q.1.1 q.1.2.1 q.1.2.2) (MvPolynomial.map A.subtype r) := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C a => rw [iS_C, map_C, aeval_C]; rfl
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp => simp only [map_mul, hp, map_X, aeval_X, iS_X]
  have hiS : Function.Injective iS := fun a b e => by
    refine MvPolynomial.map_injective A.subtype Subtype.val_injective
      ((algebraicIndependent_iff_injective_aeval.1 indep) ?_)
    rw [← eS, ← eS, e]
  let i : R →+* L := aL.comp (Polynomial.mapRingHom iS)
  have hi : Function.Injective i :=
    (IsFractionRing.injective P L).comp (Polynomial.map_injective iS hiS)
  let ρ₀ : Q →+* ℂ := eval₂Hom val fun q => h q.1.1 q.1.2.1 q.1.2.2
  let ρ : R →+* ℂ := Polynomial.eval₂RingHom ρ₀ t
  let cQ : Q →+* R := Polynomial.C
  let cA : A →+* R := cQ.comp (C : A →+* Q)
  let B : Ψ → Matrix (Fin N) (Fin N) R := fun τ' => (genericBlockMatrix A N j τ').map cQ
  have hGb : ∀ τ', IsBlockDiag j (G' τ') := fun τ' =>
    ((((hT τ').1.inv (hT τ').2.isUnit)).map _).mul (((hgb τ').map _).mul (genUp_blockDiag τ'))
  have hiG : ∀ τ', (genericBlockMatrix A N j τ').map iS = G' τ' := generic_block_matrix_map iS hGb fun q => by simp [iS]
  have hρ : ∀ τ', (genericBlockMatrix A N j τ').map ρ₀ = h τ' := generic_block_matrix_map ρ₀ hh fun q => by simp [ρ₀]
  have hdiag : ∀ τ' c, genUp Φ N j τ' c c ≠ 0 := fun τ' c => by
    rw [show genUp Φ N j τ' c c = X ⟨(τ', c, c), le_rfl, Iff.rfl⟩ from
      genUp_apply (⟨(τ', c, c), le_rfl, Iff.rfl⟩ : UpIdx Ψ N j)]
    exact X_ne_zero _
  have hinj : Function.Injective (aL.comp cP) :=
    (IsFractionRing.injective P L).comp Polynomial.C_injective
  have hle : ca ≤ cb := by
    rw [Fin.le_def]; omega
  obtain ⟨θ, hθ₁, hθ₂, hθ₃⟩ := GlobalTheory.CompanionTheory.Ar.Moebius.exists_ratFunc_embedding_moebius Φ S₀ (genUp Φ N j τ ca ca) (genUp Φ N j τ ca cb)
    (genUp Φ N j τ cb cb) (hdiag τ ca) (hdiag τ cb)
  refine ⟨L, R, inferInstance, inferInstance, φ, θ, U, s, i, ρ, cA, B, Polynomial.X, hi, hθ₁,
    fun τ' => ⟨(genUp_blockDiag τ').map _, fun a b hab => ?_, fun c => ?_⟩, hθ₂, hθ₃, fun a => ?_, fun a => ?_,
    fun τ' => (?_ : IsBlockDiag j _), fun τ' => ?_, fun τ' => ?_, ?_, ?_⟩
  · show (aL.comp cP) (genUp Φ N j τ' a b) = 0
    rw [genUp_upper τ' hab, map_zero]
  · show (aL.comp cP) (genUp Φ N j τ' c c) ≠ 0
    exact fun e => hdiag τ' c (hinj (by rw [e, map_zero]))
  · show aL (Polynomial.map iS (Polynomial.C (C a))) = aL (cP (C (algebraMap Ω Φ a)))
    rw [Polynomial.map_C]
    congr 2
    exact (eval₂Hom_C _ _ _).trans (MvPolynomial.algebraMap_apply ..)
  · show Polynomial.eval₂ ρ₀ t (Polynomial.C (C a)) = val a
    rw [Polynomial.eval₂_C]
    exact eval₂Hom_C _ _ _
  · exact (IsBlockDiag.map (fun a b hab => by
      simp [genericBlockMatrix, hab]) cQ)
  · have e1 : (B τ').map i = (G' τ').map (aL.comp cP) := by
      rw [← hiG]
      ext a b
      show aL (Polynomial.map iS (Polynomial.C _)) = aL (cP (iS _))
      rw [Polynomial.map_C]
    rw [e1]
    simp only [G', Matrix.map_mul]
    congr 1
  · rw [← hρ]
    ext a b
    show Polynomial.eval₂ ρ₀ t (Polynomial.C _) = _
    rw [Polynomial.eval₂_C]
    rfl
  · show aL (Polynomial.map iS Polynomial.X) = aL Polynomial.X
    rw [Polynomial.map_X]
  · show Polynomial.eval₂ ρ₀ t Polynomial.X = t
    rw [Polynomial.eval₂_X]

end GlobalTheory.CompanionTheory.Ar.PB.CPts.GenData
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloMapOfLocalProductCharts
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord

theorem holoMap_of_coord : ∀ (e n : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e X) (B : FinHolAtlas n Y) (pr : X → Y), (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin B.n) (σ : Fin n → Fin e), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∀ x' ∈ ψ.source, pr x' ∈ (B.chart kb).source ∧ ∀ i, B.chart kb (pr x') i = ψ x' (σ i)) → HoloMap A B pr := by
  intro e n X Y _ _ A B pr hloc
  have key : ∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin B.n) (σ : Fin n → Fin e),
      IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∀ x' ∈ ψ.source, pr x' ∈ (B.chart kb).source ∧
        pr x' = (B.chart kb).symm (fun i => ψ x' (σ i)) ∧ (fun i => ψ x' (σ i)) ∈ (B.chart kb).target := by
    intro x
    obtain ⟨ψ, kb, σ, hψ, hx, h⟩ := hloc x
    refine ⟨ψ, kb, σ, hψ, hx, fun x' hx' => ?_⟩
    obtain ⟨hs, hc⟩ := h x' hx'
    have hfun : (fun i => ψ x' (σ i)) = B.chart kb (pr x') := funext fun i => (hc i).symm
    refine ⟨hs, ?_, ?_⟩
    · rw [hfun, (B.chart kb).left_inv hs]
    · rw [hfun]
      exact (B.chart kb).map_source hs
  refine ⟨?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨ψ, kb, σ, -, hx, h⟩ := key x
    let L : (Fin e → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ i)
    have hcont : ContinuousOn ((B.chart kb).symm ∘ L ∘ ψ) ψ.source :=
      (B.chart kb).continuousOn_symm.comp (L.continuous.comp_continuousOn ψ.continuousOn)
        (fun x' hx' => (h x' hx').2.2)
    have heq : ((B.chart kb).symm ∘ L ∘ ψ) =ᶠ[𝓝 x] pr :=
      Filter.eventually_of_mem (ψ.open_source.mem_nhds hx) fun x' hx' => ((h x' hx').2.1).symm
    exact (hcont.continuousAt (ψ.open_source.mem_nhds hx)).congr heq
  · intro j k y hy
    obtain ⟨hyt, hys⟩ := hy
    obtain ⟨ψ, kb, σ, hψ, hx, h⟩ := key ((A.chart j).symm y)
    let L : (Fin e → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ i)
    have h1 : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y := (hψ j).1 y ⟨hyt, hx⟩
    have h2 : AnalyticAt ℂ (B.chart k ∘ (B.chart kb).symm) (L (ψ ((A.chart j).symm y))) := by
      apply B.holo kb k
      refine ⟨(h _ hx).2.2, ?_⟩
      show (B.chart kb).symm (fun i => ψ ((A.chart j).symm y) (σ i)) ∈ (B.chart k).source
      rw [← (h _ hx).2.1]
      exact hys
    have h3 : AnalyticAt ℂ ((B.chart k ∘ (B.chart kb).symm) ∘ L ∘ (ψ ∘ (A.chart j).symm)) y :=
      AnalyticAt.comp (f := L ∘ (ψ ∘ (A.chart j).symm)) h2
        (AnalyticAt.comp (f := ψ ∘ (A.chart j).symm) (L.analyticAt _) h1)
    apply h3.congr
    have hnb : ∀ᶠ y' in 𝓝 y, (A.chart j).symm y' ∈ ψ.source :=
      (A.chart j).continuousAt_symm hyt (ψ.open_source.mem_nhds hx)
    filter_upwards [hnb] with y' hy'
    simp only [Function.comp_apply]
    rw [(h _ hy').2.1]
    rfl

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicConjugatePullbackStatement
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_conjugate_pullback : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} (c : X → X), Continuous c → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → ∀ {V : Set X} {g : X → ℂ}, A.HoloOn V g → A.HoloOn (c ⁻¹' V) (fun y => starRingEnd ℂ (g (c y))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.holoOn_conj_comp | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.holoOn_conj_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.holoOn_conj_comp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsNullOfLocallyInZeros
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.NullLocal

theorem isNull_of_locally_in_zeros (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (Z : Set X)
    (hZ : ∀ x ∈ Z, ∃ (W : Set X) (f : X → ℂ), IsOpen W ∧ x ∈ W ∧ A.HoloOn W f ∧
      (∀ y ∈ W ∩ Z, f y = 0) ∧ ∀ V, IsOpen V → V.Nonempty → V ⊆ W → ∃ y ∈ V, f y ≠ 0) :
    IsNull A Z := by
  intro j
  refine measure_null_of_locally_null _ fun w hw => ?_
  obtain ⟨hwt, hwZ⟩ := hw
  obtain ⟨W, f, hWo, hxW, hf, hfZ, hne⟩ := hZ _ hwZ
  have hOo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
    (A.chart j).isOpen_inter_preimage_symm hWo
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hOo w ⟨hwt, hxW⟩
  have hV : IsOpen ((A.chart j).symm '' Metric.ball w r) :=
    (A.chart j).isOpen_image_symm_of_subset_target Metric.isOpen_ball
      fun z hz => (hrO hz).1
  obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := hne _ hV ⟨_, w, Metric.mem_ball_self hr, rfl⟩ (by
    rintro _ ⟨z, hz, rfl⟩
    exact (hrO hz).2)
  have hnull := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd (U := Metric.ball w r)
    Metric.isOpen_ball (convex_ball w r).isPreconnected
    (f := f ∘ (A.chart j).symm) ((hf j).mono hrO) ⟨z, hz, hy⟩
  refine ⟨((A.chart j).target ∩ (A.chart j).symm ⁻¹' Z) ∩ Metric.ball w r,
    inter_mem_nhdsWithin _ (Metric.ball_mem_nhds w hr), measure_mono_null ?_ hnull⟩
  rintro v ⟨⟨-, hvZ⟩, hvb⟩
  exact ⟨hvb, hfZ _ ⟨(hrO hvb).2, hvZ⟩⟩

end GlobalTheory.CompanionTheory.Ar.PB.NullLocal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsSmoothHermPullHerm
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.FA.StepLine

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

theorem pullDeg_zero {K K' : Type} (κ : K → K') : pullDeg κ (0 : K → ℤ) = 0 := by
  funext k
  by_cases h : ∃ a, κ a = k
  · simp [pullDeg, Function.extend_def, h]
  · simp [pullDeg, Function.extend_def, h]

theorem isSmoothHerm_pullHerm {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
    [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) {B : HermLine ι} (hB : IsSmoothHerm B) : IsSmoothHerm (pullHerm hv B) := by
  have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k', ι' k') → ℂ => fun q => z (v q)) :=
    contDiff_pi.2 fun q => contDiff_apply ℝ (fun _ => ℂ) (v q)
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B.h ∘ fun z : (Σ k', ι' k') → ℂ => fun q => z (v q))
    {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  refine ContDiffOn.comp hB hlin.contDiffOn ?_
  intro z hz k
  obtain ⟨i', hi'⟩ := hz (κ k)
  obtain ⟨q, hq⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : q.1 = k := hv.1 (by rw [← hv.2.2.1 q, hq])
  obtain ⟨k₀, m⟩ := q
  simp only at h2
  subst h2
  exact ⟨m, by simpa [hq] using hi'⟩

theorem exists_stepLine : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (p : Ψ × Fin N)
    (B : HermLine (stepIdx M p)), B.a = 0 → ∃ A : HermLine ι, A.a = M.dy p ∧ M.OnStep p A ∧
      (IsSmoothHerm B → IsSmoothHerm A) ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
        Real.log (A.h z) = Real.log ((fsHerm ι (M.dy p)).h z) + Real.log (B.h (z ∘ stepV M p)) := by
  intro K _ ι _ Φ _ y Ψ N j M p B hB
  have hdy : ∀ k, M.dy p k ≠ 0 → k ∈ Set.range (Subtype.val : PartialFlagBlocks M p → K) := by
    intro k hk
    by_cases h : ∀ p', M.blk p' ≠ some k
    · exact ⟨⟨k, Or.inl h⟩, rfl⟩
    · by_cases h' : M.blk p = some k
      · exact ⟨⟨k, Or.inr h'⟩, rfl⟩
      · exact absurd (show M.dy p k = 0 by unfold FlagModel.dy; rw [dite_eq_right h, if_neg h']) hk
  refine ⟨(fsHerm ι (M.dy p)).tensor (pullHerm (isBlockMap_stepV M p) B), ?_, ?_, ?_, ?_⟩
  · show M.dy p + pullDeg _ B.a = M.dy p
    rw [hB, pullDeg_zero, add_zero]
  · intro z z' hb hs
    have hc : z ∘ stepV M p = z' ∘ stepV M p := by
      funext ⟨⟨k, hk⟩, m⟩
      rcases hk with h | h
      · exact congrFun hb ⟨⟨k, h⟩, m⟩
      · exact hs k h m
    show (fsHerm ι (M.dy p)).h z * B.h (z ∘ stepV M p) = (fsHerm ι (M.dy p)).h z' * B.h (z' ∘ stepV M p)
    rw [StepW.fsHerm_h_blockMap K ι (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) (M.dy p) z
        (isBlockMap_stepV M p) hdy,
      StepW.fsHerm_h_blockMap K ι (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) (M.dy p) z'
        (isBlockMap_stepV M p) hdy, hc]
  · intro hS
    exact isSmoothHerm_tensor (FlagHeightMultilinear.isSmoothHerm_fsHerm _)
      (isSmoothHerm_pullHerm (isBlockMap_stepV M p) hS)
  · intro z hz
    have h1 := (fsHerm ι (M.dy p)).pos z hz
    have h2 := (pullHerm (isBlockMap_stepV M p) B).pos z hz
    exact Real.log_mul h1.ne' h2.ne'

end GlobalTheory.CompanionTheory.Ar.PB.FA.StepLine
end

