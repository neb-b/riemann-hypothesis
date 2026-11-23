module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE

open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem chi_norm (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : ‖X.χ la γ‖ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  have h1 := congrArg norm (h γ hγ)
  rw [norm_pow, norm_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h1

theorem bchar_ne (la : Wt X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : bchar la b ≠ 0 := by
  have hb' : ∀ τ : X.Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 := hb
  unfold bchar
  rw [Finset.prod_ne_zero_iff]
  intro τ _
  rw [Finset.prod_ne_zero_iff]
  intro i _
  have hd := (hb' τ).1
  have hbt : (mat b τ).BlockTriangular id := fun a c hca => (hb' τ).2 a c hca
  rw [Matrix.det_of_upperTriangular hbt, Finset.prod_ne_zero_iff] at hd
  have hi := hd i (Finset.mem_univ _)
  exact zpow_ne_zero _ hi


open Classical in
def phiF (f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞) : Frame X.Ψ r → ℝ≥0∞ :=
  fun y => X.dom.piecewise (fun y => ENNReal.ofReal (‖f0 y‖ ^ 2)) 0 y * W y

theorem phiF_dom (f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phiF X f0 W x = ENNReal.ofReal (‖f0 x‖ ^ 2) * W x := by
  simp [phiF, Set.piecewise, hx]

theorem phiF_meas {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞} (hf : ContinuousOn f0 X.dom)
    (hW : Measurable W) : Measurable (phiF X f0 W) := by
  classical
  have hopen : IsOpen X.dom := by
    have h1 : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
        ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
      rfl
    rw [h1]
    refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
    · refine isOpen_ne_fun ?_ continuous_const
      unfold mat
      fun_prop
    · refine isOpen_lt continuous_const ?_
      unfold dmin lminor ReciprocityTheory.ChartRestriction.G.FD.gram ReciprocityTheory.ChartRestriction.G.FD.hermC ReciprocityTheory.ChartRestriction.G.FD.col mat
      fun_prop
  unfold phiF
  refine Measurable.mul ?_ hW
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hopen.measurableSet
  exact ENNReal.continuous_ofReal.comp_continuousOn (hf.norm.pow 2)

theorem phiF_B {la : Wt X.Ψ r} {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hf0 : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, f0 (rmul x b) = bchar la b * f0 x)
    (hW : IsMetricW X la W) : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, phiF X f0 W (rmul x b) = phiF X f0 W x := by
  intro x hx b hb
  rw [phiF_dom X f0 W (dom_rmul X hx hb), phiF_dom X f0 W hx, hf0 x hx b hb, hW.2.1 x hx b hb,
    norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
  have hA0 : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos (norm_pos_iff.2 (bchar_ne X la hb)) 2
  have hAt : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.div_eq_inv_mul]
  calc ENNReal.ofReal (‖bchar la b‖ ^ 2) * ENNReal.ofReal (‖f0 x‖ ^ 2) *
        ((ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹ * W x)
      = ENNReal.ofReal (‖f0 x‖ ^ 2) * W x *
          (ENNReal.ofReal (‖bchar la b‖ ^ 2) * (ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹) := by ring
    _ = ENNReal.ofReal (‖f0 x‖ ^ 2) * W x := by rw [ENNReal.mul_inv_cancel hA0 hAt, mul_one]

theorem phiF_G {la : Wt X.Ψ r} {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hf0 : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, f0 (lact γ x) = X.χ la γ * f0 x)
    (hW : IsMetricW X la W) : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, phiF X f0 W (lact γ x) = phiF X f0 W x := by
  intro γ hγ x hx
  rw [phiF_dom X f0 W (dom_lact X hγ hx), phiF_dom X f0 W hx, hf0 γ hγ x hx, hW.2.2 γ hγ x hx,
    norm_mul, chi_norm X la hγ, one_mul]

variable (x0 : Frame X.Ψ r)

theorem nfac_pos {la : Wt X.Ψ r} {z : V (nd X)} (hz : z ∈ OmF X x0) : 0 < X.nfac la (cpt X x0 z) := by
  have hz' : ∀ τ : X.Ψ, (mat (cpt X x0 z) τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (cpt X x0 z) τ i).re := hz
  have hd : ∀ τ i, dmin X.Gm (cpt X x0 z) τ i ≠ 0 := by
    intro τ i h
    have h2 := (hz' τ).2 i
    rw [h, Complex.zero_re, mul_zero] at h2
    exact lt_irrefl _ h2
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
  apply Finset.prod_pos
  intro τ _
  apply Finset.prod_pos
  intro i _
  exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _))) _

theorem nfac_cont (la : Wt X.Ψ r) : ContinuousOn (fun z => X.nfac la (cpt X x0 z)) (OmF X x0) := by
  have hn : Continuous fun z : V (nd X) => nmat X z := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    unfold nmat
    by_cases h : b < a
    · simp only [h, dif_pos]
      fun_prop
    · simp only [h, dif_neg, not_false_eq_true]
      exact continuous_const
  have hc : Continuous fun z : V (nd X) => cpt X x0 z := by
    refine continuous_pi fun τ => ?_
    show Continuous fun z : V (nd X) => mat x0 τ * mat (nmat X z) τ
    exact continuous_const.matrix_mul ((continuous_apply τ).comp hn)
  have hd : ∀ τ i, Continuous fun z : V (nd X) => dmin X.Gm (cpt X x0 z) τ i := by
    intro τ i
    have h1 : Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
      unfold dmin lminor ReciprocityTheory.ChartRestriction.G.FD.gram ReciprocityTheory.ChartRestriction.G.FD.hermC ReciprocityTheory.ChartRestriction.G.FD.col mat
      fun_prop
    exact h1.comp hc
  have hne : ∀ z ∈ OmF X x0, ∀ τ i, dmin X.Gm (cpt X x0 z) τ i ≠ 0 := by
    intro z hz τ i h
    have hz' : ∀ τ : X.Ψ, (mat (cpt X x0 z) τ).det ≠ 0 ∧
        ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (cpt X x0 z) τ i).re := hz
    have h2 := (hz' τ).2 i
    rw [h, Complex.zero_re, mul_zero] at h2
    exact lt_irrefl _ h2
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
  apply continuousOn_finsetProd
  intro τ _
  apply continuousOn_finsetProd
  intro i _
  intro z hz
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.rpow_const
  · exact ((hd τ _).continuousAt.div (hd τ _).continuousAt (hne z hz τ _)).norm
  · left
    exact norm_ne_zero_iff.mpr (div_ne_zero (hne z hz τ _) (hne z hz τ _))

theorem expPhla_cont (la : Wt X.Ψ r) :
    ContinuousOn (fun z => Real.exp (-phla X la (cpt X x0 z))) (OmF X x0) := by
  unfold phla
  have h1 := nfac_cont X x0 la
  exact (continuousOn_const.mul (h1.log fun z hz => (nfac_pos X x0 (la := la) hz).ne')).neg.rexp

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradStatementPfB
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD

variable {n : ℕ}

theorem leviV_const (c : ℝ) (x : V n) (ξ : Fin n → ℂ) :
    leviV n (fun _ => (c : ℂ)) x ξ = 0 := by
  have h : ∀ k, wdb n k (fun _ : V n => (c : ℂ)) = fun _ => 0 := by
    intro k; funext y; simp [wdb]
  simp [leviV, h, wd]

theorem quad_contDiff {r s : ℕ} (τ : ℝ) (ℓ : Fin r → Fin s → V n → ℂ)
    (hℓ : ∀ a b, ContDiff ℂ ∞ (ℓ a b)) :
    ContDiff ℝ ∞ (fun y => τ - ∑ a, ∑ b, Complex.normSq (ℓ a b y)) := by
  refine contDiff_const.sub (ContDiff.sum fun a _ => ContDiff.sum fun b _ => ?_)
  simp only [Complex.normSq_eq_norm_sq]
  exact (contDiff_norm_sq ℝ).comp ((hℓ a b).restrict_scalars ℝ)

theorem levi_quad_nonpos {r s : ℕ} (τ : ℝ) (ℓ : Fin r → Fin s → V n → ℂ)
    (hℓ : ∀ a b, ContDiff ℂ ∞ (ℓ a b)) (x : V n) (ξ : Fin n → ℂ) :
    (leviV n (fun y => ((τ - ∑ a, ∑ b, Complex.normSq (ℓ a b y) : ℝ) : ℂ)) x ξ).re ≤ 0 := by
  have hc : ∀ a b, ContDiffAt ℝ 2 (fun y => Complex.normSq (ℓ a b y)) x := by
    intro a b
    have h := quad_contDiff (r := 1) (s := 1) 0 (fun _ _ => ℓ a b) (fun _ _ => hℓ a b)
    have h2 : ContDiff ℝ ∞ (fun y => Complex.normSq (ℓ a b y)) := by
      have := h.neg
      simpa using this
    exact h2.contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)
  have hca : ∀ a, ContDiffAt ℝ 2 (fun y => ∑ b, Complex.normSq (ℓ a b y)) x := fun a =>
    ContDiffAt.sum fun b _ => hc a b
  have hS : ContDiffAt ℝ 2 (fun y => ∑ a, ∑ b, Complex.normSq (ℓ a b y)) x :=
    ContDiffAt.sum fun a _ => hca a
  have e1 : (fun y => ((τ - ∑ a, ∑ b, Complex.normSq (ℓ a b y) : ℝ) : ℂ)) =
      fun y => ((τ + (-1) * ∑ a, ∑ b, Complex.normSq (ℓ a b y) : ℝ) : ℂ) := by
    funext y; push_cast; ring
  rw [e1, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add contDiffAt_const (contDiffAt_const.mul hS) ξ,
    leviV_const, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-1) hS ξ,
    ReciprocityTheory.L2DbarEstimates.leviV_ofReal_sum hca ξ]
  simp only [ReciprocityTheory.L2DbarEstimates.leviV_ofReal_sum (fun b => hc _ b) ξ]
  simp only [ReciprocityTheory.L2DbarEstimates.H.leviV_normSq_comp ((hℓ _ _).contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)) ξ]
  simp only [zero_add, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.re_sum,
    Complex.im_sum, zero_mul, sub_zero]
  have : 0 ≤ ∑ a : Fin r, ∑ b : Fin s, Complex.normSq (∑ j, wd n j (ℓ a b) x * ξ j) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _
  nlinarith

theorem trace_mul_conjTranspose_re {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℂ) :
    (B * Bᴴ).trace.re = ∑ a, ∑ b, Complex.normSq (B a b) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum,
    Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

theorem Q_formula {r s : ℕ} (Z : Matrix (Fin r) (Fin s) ℂ) (y : Matrix (Fin r) (Fin r) ℂ) :
    ((1 - Z * Zᴴ) * (yᴴ * y)).trace.re =
      (yᴴ * y).trace.re - ∑ a, ∑ b, Complex.normSq ((y * Z) a b) := by
  rw [← trace_mul_conjTranspose_re, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
    Complex.sub_re]
  congr 2
  rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem posDef_swap {r s : ℕ} {Z : Matrix (Fin r) (Fin s) ℂ} (h : (1 - Z * Zᴴ).PosDef) :
    (1 - Zᴴ * Z).PosDef := by
  have hu : IsUnit (1 - Z * Zᴴ).det := isUnit_iff_ne_zero.2 h.det_pos.ne'
  set S := (1 - Z * Zᴴ)⁻¹ with hS
  have hAS : (1 - Z * Zᴴ) * S = 1 := Matrix.mul_nonsing_inv _ hu
  have key : (1 - Zᴴ * Z) * (1 + Zᴴ * S * Z) = 1 := by
    have e : (1 - Zᴴ * Z) * (1 + Zᴴ * S * Z) = 1 + Zᴴ * ((1 - Z * Zᴴ) * S - 1) * Z := by
      simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_assoc]
      abel
    rw [e, hAS, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  have hinv : (1 - Zᴴ * Z)⁻¹ = 1 + Zᴴ * S * Z := Matrix.inv_eq_right_inv key
  have hP : (1 + Zᴴ * S * Z).PosDef :=
    PosDef.one.add_posSemidef ((h.inv).posSemidef.conjTranspose_mul_mul_same Z)
  rw [← hinv] at hP
  exact Matrix.posDef_inv_iff.1 hP

end ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgD

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

variable {f p q : ℕ}

theorem block (hm : 0 < min p q) {v0 : V (nD f p q)} (hv0 : v0 ∈ Dset f p q) (k : Fin f) :
    ∃ Q : V (nD f p q) → ℝ, ContDiff ℝ ∞ Q ∧
      (∀ ξ, (leviV (nD f p q) (fun y => (Q y : ℂ)) v0 ξ).re ≤ 0) ∧
      Q v0 = (min p q : ℕ) ∧
      ∀ v ∈ Dset f p q, dk v k ^ (((min p q : ℕ) : ℝ)⁻¹) ≤
        dk v0 k ^ (((min p q : ℕ) : ℝ)⁻¹) * (Q v / (min p q : ℕ)) := by
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq] at hm ⊢
    have hA0 := hv0 k
    obtain ⟨y, hy⟩ := RgB.exists_factor hA0.inv.posSemidef
    set Q : V (nD f p q) → ℝ := fun v =>
      ((1 - Zof v k * (Zof v k)ᴴ) * (1 - Zof v0 k * (Zof v0 k)ᴴ)⁻¹).trace.re with hQdef
    have hℓ : ∀ a b, ContDiff ℂ ∞ (fun v : V (nD f p q) => (y * Zof v k) a b) := by
      intro a b
      simp only [Matrix.mul_apply, Zof, Matrix.of_apply]
      exact ContDiff.sum fun c _ => contDiff_const.mul (cd_coord _)
    have hQ : Q = fun v => (yᴴ * y).trace.re -
        ∑ a, ∑ b, Complex.normSq ((fun a b (v : V (nD f p q)) => (y * Zof v k) a b) a b v) := by
      funext v; simp only [hQdef]; rw [hy, Q_formula]
    refine ⟨Q, ?_, ?_, ?_, ?_⟩
    · rw [hQ]; exact quad_contDiff _ _ hℓ
    · intro ξ; rw [hQ]; exact levi_quad_nonpos _ _ hℓ v0 ξ
    · simp only [hQdef]
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA0.det_pos.ne')]
      simp
    · intro v hv
      exact RgB.amgm hm (hv k) hA0
  · rw [min_eq_right hqp] at hm ⊢
    have hA0 := posDef_swap (hv0 k)
    obtain ⟨y, hy⟩ := RgB.exists_factor hA0.inv.posSemidef
    set Q : V (nD f p q) → ℝ := fun v =>
      ((1 - (Zof v k)ᴴ * Zof v k) * (1 - (Zof v0 k)ᴴ * Zof v0 k)⁻¹).trace.re with hQdef
    have hℓ : ∀ a b, ContDiff ℂ ∞
        (fun v : V (nD f p q) => ∑ c, star (y a c) * Zof v k b c) := by
      intro a b
      simp only [Zof, Matrix.of_apply]
      exact ContDiff.sum fun c _ => contDiff_const.mul (cd_coord _)
    have hQ : Q = fun v => (yᴴ * y).trace.re - ∑ a, ∑ b, Complex.normSq
        ((fun a b (v : V (nD f p q)) => ∑ c, star (y a c) * Zof v k b c) a b v) := by
      funext v
      simp only [hQdef]
      have h1 := Q_formula (Zof v k)ᴴ y
      rw [Matrix.conjTranspose_conjTranspose] at h1
      rw [hy, h1]
      congr 1
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [← Complex.normSq_conj]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mul_apply, conjTranspose_apply, map_sum, Complex.star_def, mul_comm]
    refine ⟨Q, ?_, ?_, ?_, ?_⟩
    · rw [hQ]; exact quad_contDiff _ _ hℓ
    · intro ξ; rw [hQ]; exact levi_quad_nonpos _ _ hℓ v0 ξ
    · simp only [hQdef]
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA0.det_pos.ne')]
      simp
    · intro v hv
      have h := RgB.amgm hm (posDef_swap (hv k)) hA0
      simp only [dk]
      rw [Matrix.det_one_sub_mul_comm, Matrix.det_one_sub_mul_comm (Zof v0 k)]
      exact h

end ReciprocityTheory.ChartRestriction.G.AR.Up.RgD
end

