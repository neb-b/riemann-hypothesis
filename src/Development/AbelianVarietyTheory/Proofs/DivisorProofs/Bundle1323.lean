module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0227

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBallExtendByZeroInvariant
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ChartBallExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def InOrbit (X : Data E r) (x : Frame X.Ψ r) (R : ℝ) (y : Frame X.Ψ r) : Prop :=
  ∃ z : V (nd X), ‖z‖ ≤ R ∧ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul (cpt X x z) b)


open Classical in
noncomputable def ext (X : Data E r) (x : Frame X.Ψ r) (R : ℝ) (η : V (nd X) → ℝ) (y : Frame X.Ψ r) : ℝ :=
  if h : InOrbit X x R y then η h.choose else 0

theorem uniq (X : Data E r) {x : Frame X.Ψ r} {R : ℝ} (ho : IsOrth X x)
    (hinj : ∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r,
      lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1)
    {γ γ' : GL (Fin r) E} (hγ : γ ∈ X.Γ) (hγ' : γ' ∈ X.Γ) {b b' : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) {z z' : V (nd X)} (hz : ‖z‖ ≤ R) (hz' : ‖z'‖ ≤ R)
    (h : lact γ (rmul (cpt X x z) b) = lact γ' (rmul (cpt X x z') b')) : z = z' := by
  have h1 : lact (γ'⁻¹ * γ) (rmul (cpt X x z) b) = rmul (cpt X x z') b' := by
    rw [← IW.lact_lact, h, IW.lact_lact, inv_mul_cancel, IW.lact_one]
  have h2 : lact (γ'⁻¹ * γ) (cpt X x z) = rmul (cpt X x z') (IW.bmul X b' (IW.binv X b)) := by
    rw [← IW.rmul_rmul, ← h1, IW.lact_rmul, IW.rmul_binv X _ hb]
  have h3 := hinj _ (X.Γ.mul_mem (X.Γ.inv_mem hγ') hγ) z z' hz hz' _
    (IW.bmul_mem X hb' (IW.binv_mem X hb)) h2
  rw [h3, IW.lact_one] at h1
  exact (KU.cpt_inj X ho hb hb' h1).1

theorem ext_val (X : Data E r) {x : Frame X.Ψ r} {R : ℝ} (ho : IsOrth X x)
    (hinj : ∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r,
      lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1)
    (η : V (nd X) → ℝ) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    {z : V (nd X)} (hz : ‖z‖ ≤ R) : ext X x R η (lact γ (rmul (cpt X x z) b)) = η z := by
  have hP : InOrbit X x R (lact γ (rmul (cpt X x z) b)) := ⟨z, hz, γ, hγ, b, hb, rfl⟩
  unfold ext
  rw [dite_eq_left hP]
  obtain ⟨hz', γ', hγ', b', hb', he⟩ := hP.choose_spec
  rw [uniq X ho hinj hγ' hγ hb' hb hz' hz he.symm]

theorem ext_zero (X : Data E r) {x : Frame X.Ψ r} {R : ℝ} (η : V (nd X) → ℝ) {y : Frame X.Ψ r}
    (hy : ¬ InOrbit X x R y) : ext X x R η y = 0 := by
  unfold ext
  rw [dite_eq_right hy]

end GlobalTheory.ChartBallExt


open GlobalTheory.ChartBallExt in
theorem GlobalTheory.chartBall_extend_by_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (R : ℝ), IsOrth X x → (∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x) → (∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1) → ∀ η : V (nd X) → ℝ, ∃ ψ : Frame X.Ψ r → ℝ, (∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z) ∧ (∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ R ∧ y = lact γ (rmul (cpt X x z) b)) → ψ y = 0) ∧ (∀ γ ∈ X.Γ, ∀ y, ψ (lact γ y) = ψ y) ∧ (∀ y, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y) := by
  intro E _ _ _ r X x R ho _ hinj η
  refine ⟨ext X x R η, ?_, ?_, ?_, ?_⟩
  · intro γ hγ b hb z hz
    exact ext_val X ho hinj η hγ hb hz
  · intro y hy
    refine ext_zero X η ?_
    rintro ⟨z, hz, γ, hγ, b, hb, e⟩
    exact hy ⟨γ, hγ, b, hb, z, hz, e⟩
  · intro γ hγ y
    by_cases hy : InOrbit X x R y
    · obtain ⟨z, hz, γ0, hγ0, b, hb, rfl⟩ := hy
      rw [IW.lact_lact, ext_val X ho hinj η (X.Γ.mul_mem hγ hγ0) hb hz, ext_val X ho hinj η hγ0 hb hz]
    · have hy' : ¬ InOrbit X x R (lact γ y) := by
        rintro ⟨z, hz, γ0, hγ0, b, hb, e⟩
        refine hy ⟨z, hz, γ⁻¹ * γ0, X.Γ.mul_mem (X.Γ.inv_mem hγ) hγ0, b, hb, ?_⟩
        rw [← IW.lact_lact, ← e, IW.lact_lact, inv_mul_cancel, IW.lact_one]
      rw [ext_zero X η hy, ext_zero X η hy']
  · intro y b hb
    by_cases hy : InOrbit X x R y
    · obtain ⟨z, hz, γ0, hγ0, b0, hb0, rfl⟩ := hy
      rw [← IW.lact_rmul, IW.rmul_rmul, ext_val X ho hinj η hγ0 (IW.bmul_mem X hb0 hb) hz,
        ext_val X ho hinj η hγ0 hb0 hz]
    · have hy' : ¬ InOrbit X x R (rmul y b) := by
        rintro ⟨z, hz, γ0, hγ0, b0, hb0, e⟩
        refine hy ⟨z, hz, γ0, hγ0, IW.bmul X b0 (IW.binv X b), IW.bmul_mem X hb0 (IW.binv_mem X hb), ?_⟩
        rw [← IW.rmul_rmul, IW.lact_rmul, ← e, IW.rmul_binv X y hb]
      rw [ext_zero X η hy, ext_zero X η hy']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBallWeightPotentialDensityBounds
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.WeightSizes

theorem chart_ball_sizes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) (z : V (nd X)), IsOrth X x → ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → z ∈ OmF X x ∧ |phla X la (cpt X x z)| ≤ ∑ τ, ∑ a, |(la τ a : ℝ)| ∧ |rhF X x z| ≤ (X.Ψ.card : ℝ) ∧ |Real.log (densF X x z)| ≤ (X.Ψ.card : ℝ) * r ∧ 0 < densF X x z := by
  intro E _ _ _ r X la x z hx hz
  have h : (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · norm_num
    · have hr' : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
      calc (r : ℝ) ^ 2 * ‖z‖ ≤ (r : ℝ) ^ 2 * (1 / (100 * (r : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hz hr'.le
        _ = 1 / 100 := by field_simp
  obtain ⟨hdom, hd⟩ := GlobalTheory.dmin_rmul_near_one X x hx (nmat X z) (norm_nonneg z) (by linarith)
    (fun τ a b => GlobalTheory.ChartNearOne.nmat_entry_le X z τ a b)
  change cpt X x z ∈ X.dom at hdom
  have hL : ∀ τ i, |IW.Lm X (cpt X x z) τ i| ≤ 9 / 100 := fun τ i => by
    have h9 := (hd τ i).2
    change |Real.log ‖dmin X.Gm (cpt X x z) τ i‖| ≤ _ at h9
    unfold IW.Lm
    linarith
  have hz' : z ∈ OmF X x := hdom
  refine ⟨hz', ?_, ?_, ?_, ?_⟩
  · rw [IW.phla_eq X hdom la]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    have h1 : |IW.Lm X (cpt X x z) τ i.succ - IW.Lm X (cpt X x z) τ i.castSucc| ≤ 1 := by
      have ha := abs_le.1 (hL τ i.succ)
      have hb := abs_le.1 (hL τ i.castSucc)
      rw [abs_le]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    calc |(la τ i : ℝ)| * _ ≤ |(la τ i : ℝ)| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = _ := mul_one _
  · unfold rhF
    rw [abs_neg]
    have hs : ∑ τ : X.Ψ, |Real.log ‖dmin X.Gm (cpt X x z) τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖| ≤
        ∑ _τ : X.Ψ, (1 : ℝ) := Finset.sum_le_sum fun τ _ => by
      have h9 := hL τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
      unfold IW.Lm at h9
      linarith
    refine (Finset.abs_sum_le_sum_abs _ _).trans (hs.trans ?_)
    simp
  · rw [IW.log_densF_eq X x hz']
    have hs : ∑ τ : X.Ψ, ∑ i : Fin r, |(-2) * IW.Lm X (cpt X x z) τ i.castSucc| ≤
        ∑ _τ : X.Ψ, ∑ _i : Fin r, (1 : ℝ) := Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => by
      have h9 := hL τ i.castSucc
      rw [abs_mul]
      norm_num
      linarith
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun τ _ => Finset.abs_sum_le_sum_abs _ _).trans (hs.trans ?_))
    simp
  · unfold densF
    exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
      zpow_pos (norm_pos_iff.2 (IW.dmin_ne_zero X hdom τ _)) _

end GlobalTheory.WeightSizes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFirstColumnsEqGraphTimesTopBlock
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph

namespace GlobalTheory.ChartGraph

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem chartMatrixTopBlock_det_eq_one (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : (chartMatrixTopBlock X z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (chartMatrixTopBlock X z τ) (by
    intro i j hij
    have hij' : i < j := hij
    show nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j) = 0
    have h1 : ¬ (Fin.castLE X.p0_le j < Fin.castLE X.p0_le i) := by
      rw [Fin.lt_iff_val_lt_val]; simp only [Fin.coe_castLE]; exact not_lt.mpr (le_of_lt hij')
    have h2 : Fin.castLE X.p0_le i ≠ Fin.castLE X.p0_le j := by
      intro h; apply ne_of_lt hij'; exact Fin.castLE_injective _ h
    simp only [nmat, dif_neg h1, if_neg h2])]
  apply Finset.prod_eq_one
  intro i _
  show nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le i) = 1
  simp [nmat]

theorem entry_eq (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (m : Fin r) (a : Fin X.p0) :
    nmat X z τ m (Fin.castLE X.p0_le a) =
      ∑ c : Fin X.p0, X.lowBlock (graphCoord X z) τ m (Fin.castLE X.p0_le c) * chartMatrixTopBlock X z τ c a := by
  by_cases hm : (m : ℕ) < X.p0
  · have hrow : ∀ c : Fin X.p0, X.lowBlock (graphCoord X z) τ m (Fin.castLE X.p0_le c) =
        if (⟨m, hm⟩ : Fin X.p0) = c then 1 else 0 := by
      intro c
      simp only [Data.lowBlock, Matrix.of_apply]
      rw [dif_neg (by omega)]
      simp only [add_zero]
      congr 1
      apply propext
      constructor
      · intro h
        have hv : (m : ℕ) = (c : ℕ) := by simpa using congrArg (fun t : Fin r => (t : ℕ)) h
        exact Fin.ext hv
      · intro h; ext; rw [← h]; rfl
    simp only [hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  · have hm' : X.p0 ≤ (m : ℕ) := not_lt.mp hm
    have hrow : ∀ c : Fin X.p0, X.lowBlock (graphCoord X z) τ m (Fin.castLE X.p0_le c) =
        graphCoord X z τ ⟨(m : ℕ) - X.p0, by have := m.isLt; omega⟩ c := by
      intro c
      simp only [Data.lowBlock, Matrix.of_apply]
      have hne : m ≠ Fin.castLE X.p0_le c := by
        intro h; have := congrArg Fin.val h; simp at this; have := c.isLt; omega
      rw [if_neg hne, dite_eq_left ⟨hm', c.isLt⟩, zero_add]
      rfl
    simp only [hrow]
    have hdet : IsUnit (chartMatrixTopBlock X z τ).det := by rw [chartMatrixTopBlock_det_eq_one]; exact isUnit_one
    have key : chartBottomLeftBlock X z τ * (chartMatrixTopBlock X z τ)⁻¹ * chartMatrixTopBlock X z τ = chartBottomLeftBlock X z τ := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
    have := congrFun (congrFun key ⟨(m : ℕ) - X.p0, by have := m.isLt; omega⟩) a
    rw [Matrix.mul_apply] at this
    have h2 : chartBottomLeftBlock X z τ ⟨(m : ℕ) - X.p0, by have := m.isLt; omega⟩ a = nmat X z τ m (Fin.castLE X.p0_le a) := by
      show nmat X z τ ⟨X.p0 + ((m : ℕ) - X.p0), _⟩ (Fin.castLE X.p0_le a) = _
      congr 1
      ext; simp only; omega
    exact (this.trans h2).symm

theorem cols_graph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r)
    (z : V (nd X)) (τ : X.Ψ), (chartMatrixTopBlock X z τ).det = 1 ∧ ∀ a : Fin X.p0,
    col (mat (cpt X x z) τ) (Fin.castLE X.p0_le a) =
      ∑ c : Fin X.p0, chartMatrixTopBlock X z τ c a • col (mat (X.xZ x (graphCoord X z)) τ) (Fin.castLE X.p0_le c) := by
  intro E _ _ _ r X x z τ
  refine ⟨chartMatrixTopBlock_det_eq_one X z τ, fun a => ?_⟩
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  show (mat x τ * mat (nmat X z) τ) k (Fin.castLE X.p0_le a) =
    ∑ c : Fin X.p0, chartMatrixTopBlock X z τ c a * (mat x τ * X.lowBlock (graphCoord X z) τ) k (Fin.castLE X.p0_le c)
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  show mat x τ k m * nmat X z τ m (Fin.castLE X.p0_le a) = _
  rw [entry_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end GlobalTheory.ChartGraph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseMulIntersectionNumberLeSectionDimStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.choose_mul_intersectionNumber_le_sectionDim : ∀ (k : Type) [Field k] [Infinite k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (L : LB Y) (hL : L.IsLB) (N : ℕ) (b : Fin N → L.Sec), (∀ y : Y, ∃ i, y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (b i)) → ∀ (d : ℕ) (F : Y.Modules) [IsFiniteQC F], suppDim F ≤ d → ∀ (j₀ : ℤ), VanishFrom L F j₀ → ∀ m : ℕ, (m.choose d : ℤ) * GlobalTheory.interNum k F (fun _ : Fin d => L) ≤ GlobalTheory.hdim k (GlobalTheory.twistZ F L (j₀ + m)) 0 := by
  first | exact @GlobalTheory.HSCore.choose_mul_interNum_le_hdim | exact GlobalTheory.HSCore.choose_mul_interNum_le_hdim | (intros; apply GlobalTheory.HSCore.choose_mul_interNum_le_hdim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystallineStatement
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_galois_representation_crystalline : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.HeckeLAdicCharacter →
  GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.LocalLanglandsGL →
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ P : CuspSub E a, P.IsCsd →
    ∀ m : (E →+* ℂ) → Multiset ℂ, (∀ τ, P.HasInfChar τ (m τ)) → (∀ τ, (m τ).Nodup) →
    ∀ (f : ℂ) (J : (E →+* Qbar l) → Multiset ℤ),
      (∀ τ, (J τ).map (fun k : ℤ => (k : ℂ)) = (m (ι.toRingHom.comp τ)).map (fun z => f - z)) →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧
      ((∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
          P.IsLocComp w σ ∧ GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w (n := a))) → GlobalTheory.ExpFrame.CrysWith r J) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
        ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), P.IsLocComp w σ → ∀ S : Multiset ℂˣ,
          GlobalTheory.LFun.HasSatGL w σ.ρ S → ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B w →
            IsFrob (F := E) B (normV w) g →
            (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
              Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ f))).prod := by
  first | exact @GlobalTheory.CsdTwistGal.exists_galRep_csd_twist | exact GlobalTheory.CsdTwistGal.exists_galRep_csd_twist | (intros; apply GlobalTheory.CsdTwistGal.exists_galRep_csd_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSetCharPolyCoeffBounded
section
noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.LocBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_cj (w : Pl E) : Continuous (cj w) := by
  by_cases h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)
  · exact (GlobalTheory.ConjAtPlace.cj_spec w h).1
  · rw [GlobalTheory.ConjAtPlace.cj_of_not w h]; exact continuous_id

theorem continuous_nrmL (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = fun y => y := funext fun y => by simp [nrmL, hs]
    rw [e]; exact continuous_id
  · have e : nrmL n w = fun y => y * thetaGL n (cj w) y := funext fun y => by simp [nrmL, hs]
    rw [e]
    exact continuous_id.mul (GlobalTheory.ThetaPull.continuous_thetaGL (cj w) (continuous_cj w))

theorem continuous_coeff_charpoly {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem exists_bound_of_isCompact (w : Pl E) {K : Set (w.adicCompletion E)} (hK : IsCompact K) :
    ∃ m : ℕ, ∀ x ∈ K, Valued.v x ≤ WithZero.exp (m : ℤ) := by
  let U : ℕ → Set (w.adicCompletion E) := fun m => {y | Valued.v y ≤ WithZero.exp (m : ℤ)}
  have hcov : K ⊆ ⋃ m : ℕ, U m := by
    intro x _
    rcases eq_or_ne (Valued.v x) 0 with h0 | h0
    · exact Set.mem_iUnion.2 ⟨0, by simp only [U, Set.mem_setOf_eq, h0]; exact zero_le'⟩
    · refine Set.mem_iUnion.2 ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
      show Valued.v x ≤ _
      conv_lhs => rw [← WithZero.exp_log h0]
      rw [WithZero.exp_le_exp]
      omega
  have hdir : Directed (· ⊆ ·) U :=
    Monotone.directed_le fun a b hab y hy => le_trans hy (WithZero.exp_le_exp.2 (by exact_mod_cast hab))
  obtain ⟨m, hm⟩ := hK.elim_directed_cover U (fun m => GlobalTheory.PrincCong.isOpen_ball w (m : ℤ)) hcov hdir
  exact ⟨m, fun x hx => hm hx⟩

theorem bound_charpoly_nrmL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (C : Set (GLw n w)), IsCompact C →
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ ∀ y ∈ C,
      (∀ i, Valued.v ((nrmL n w y).val.charpoly.coeff i) ≤ γ) ∧
        γ⁻¹ ≤ Valued.v ((nrmL n w y).val.charpoly.coeff 0) := by
  intro E _ _ _ n w C hC
  let F : Option (Fin (n + 1)) → GLw n w → w.adicCompletion E := fun o y =>
    match o with
    | none => ((nrmL n w y)⁻¹).val.det
    | some i => (nrmL n w y).val.charpoly.coeff i
  have hF : ∀ o, Continuous (F o) := by
    rintro (_ | i)
    · exact (Units.continuous_val.comp (continuous_nrmL n w).inv).matrix_det
    · exact (continuous_coeff_charpoly n i).comp (Units.continuous_val.comp (continuous_nrmL n w))
  have hK : IsCompact (⋃ o, F o '' C) := isCompact_iUnion fun o => hC.image (hF o)
  obtain ⟨m, hm⟩ := exists_bound_of_isCompact w hK
  have hb : ∀ o, ∀ y ∈ C, Valued.v (F o y) ≤ WithZero.exp (m : ℤ) := fun o y hy =>
    hm _ (Set.mem_iUnion.2 ⟨o, Set.mem_image_of_mem _ hy⟩)
  refine ⟨WithZero.exp (m : ℤ), WithZero.exp_ne_zero, fun y hy => ⟨fun i => ?_, ?_⟩⟩
  · by_cases hi : i ≤ n
    · exact hb (some ⟨i, Nat.lt_succ_of_le hi⟩) y hy
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; omega)]
      simp
  · have h1 : Valued.v (((nrmL n w y)⁻¹).val.det) ≤ WithZero.exp (m : ℤ) := hb none y hy
    have hdet : (nrmL n w y).val.det * ((nrmL n w y)⁻¹).val.det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    have hc0 : (nrmL n w y).val.charpoly.coeff 0 = (-1) ^ n * (nrmL n w y).val.det := by
      rw [Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩,
        one_mul]
    have hv : Valued.v ((nrmL n w y).val.charpoly.coeff 0) * Valued.v (((nrmL n w y)⁻¹).val.det) = 1 := by
      rw [hc0, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, ← map_mul, hdet, map_one]
    have hne : Valued.v (((nrmL n w y)⁻¹).val.det) ≠ 0 := fun h => by
      rw [h, mul_zero] at hv; exact zero_ne_one hv
    rw [eq_inv_of_mul_eq_one_left hv]
    exact inv_anti₀ (zero_lt_iff.2 hne) h1

end GlobalTheory.LocBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteCurveArithModelClosure
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CurveClosure

open TensorProduct

theorem isReduced_pullback_localization : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S] (V : Scheme.{0}) [IsReduced V] (f : V ⟶ Sp R), IsReduced (pullback f (spMap (algebraMap R S))) := by
  intro R S _ _ _ M _ V _ f
  let 𝒰 := Scheme.Pullback.openCoverOfLeft V.affineOpenCover.openCover f (spMap (algebraMap R S))
  have : ∀ i, IsReduced (𝒰.X i) := fun i => by
    have := V.affineOpenCover.map_prop i
    have h0 : IsReduced (Spec (V.affineOpenCover.X i)) :=
      isReduced_of_isOpenImmersion (V.affineOpenCover.f i)
    have h1 := (affine_isReduced_iff _).mp h0
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (V.affineOpenCover.f i ≫ f)
    change IsReduced (pullback (V.affineOpenCover.f i ≫ f) _)
    rw [← hφ]
    letI : Algebra R (V.affineOpenCover.X i) := φ.hom.toAlgebra
    have h2 : IsReduced (V.affineOpenCover.X i ⊗[R] S) :=
      isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (V.affineOpenCover.X i) M) _ h1
    have h3 := (affine_isReduced_iff (.of (V.affineOpenCover.X i ⊗[R] S))).mpr h2
    exact isReduced_of_isOpenImmersion (pullbackSpecIso R (V.affineOpenCover.X i) S).hom
  exact IsReduced.of_openCover _ 𝒰

theorem exists_iso_red_of_range : ∀ (X G : Scheme.{0}) (g : G ⟶ X) [IsClosedImmersion g] [IsReduced G] (Z : Closeds X), Set.range g = (Z : Set X) → ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ G, e.hom ≫ g = redι Z := by
  intro X G g _ _ Z h
  have hker : Scheme.IdealSheafData.vanishingIdeal Z = g.ker := by
    rw [← InterModel.radical_ker g, ← Scheme.IdealSheafData.vanishingIdeal_support]
    congr 1
    ext1
    rw [Scheme.Hom.support_ker, g.isClosedEmbedding.isClosed_range.closure_eq, h]
  show ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ G,
    e.hom ≫ g = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  rw [hker]
  refine ⟨(asIso g.toImage).symm, ?_⟩
  rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
  exact g.toImage_imageι.symm

end GlobalTheory.CurveClosure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveModelRationalDegree
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatFibreClosure

end GlobalTheory.RatFibreClosure
end
end

