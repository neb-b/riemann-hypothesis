module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.CurvatureStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfI

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigCellPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf Topology

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bigCell_of (hLU : LUStatement (E := E)) : BigCellStatement (E := E) := by
  intro r X x0 hx0 la P hP hvan x hx
  obtain ⟨Δ, zOf, bOf, -, hdense, -, -, hdec, -⟩ := hLU r X x0 hx0

  have hgood : ∀ y ∈ X.dom, Δ y ≠ 0 → P y = 0 := by
    intro y hy hΔ
    obtain ⟨hz, hb, hyeq⟩ := hdec y hy hΔ
    have h1 : P (rmul (cpt X x0 (zOf y)) (bOf y)) = bchar la (bOf y) * P (cpt X x0 (zOf y)) :=
      hP.2 (cpt X x0 (zOf y)) hz (bOf y) hb
    have h2 : P (cpt X x0 (zOf y)) = 0 := hvan (zOf y) hz
    rw [hyeq, h1, h2, mul_zero]

  have hopen : IsOpen X.dom := by
    have hmat : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => mat x τ := by
      intro τ
      first
      | exact continuous_apply τ
      | (unfold mat; exact continuous_apply τ)
      | fun_prop
      | continuity
    have hgram : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => gram τ.1 X.Gm (mat x τ) := by
      intro τ
      refine continuous_matrix fun a b => ?_
      simp only [gram, hermC, col, Matrix.of_apply]
      have h := hmat τ
      first
      | fun_prop
      | continuity
    have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det :=
      fun τ => (hmat τ).matrix_det
    have hmin : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), Continuous fun x : Frame X.Ψ r => (dmin X.Gm x τ i).re := by
      intro τ i
      unfold dmin lminor
      exact Complex.continuous_re.comp ((hgram τ).matrix_submatrix _ _).matrix_det
    show IsOpen (GG X.Ψ X.Gm X.p0)
    have hset : GG X.Ψ X.Gm X.p0 = ⋂ τ : X.Ψ, ({x | (mat x τ).det ≠ 0} ∩
        ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
      ext x
      simp only [GG, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
    rw [hset]
    exact isOpen_iInter_of_finite fun τ => (isOpen_ne_fun (hdet τ) continuous_const).inter
      (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_const.mul (hmin τ i)))
  have hcont : ContinuousOn P X.dom := hP.1.continuousOn
  by_contra hne
  have hU : IsOpen (X.dom ∩ P ⁻¹' {0}ᶜ) := hcont.isOpen_inter_preimage hopen isOpen_compl_singleton
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x ⟨hx, hne⟩
  obtain ⟨y, hy, hΔ⟩ := hdense x hx ε hε
  have hy' := hball hy
  have h0 := hgood y hy'.1 hΔ
  exact hy'.2 h0

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CurvNumStatementPf
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf ReciprocityTheory.L2DbarEstimates Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def coefR {r : ℕ} (X : Data E r) (v : X.Ψ → Fin r → ℝ) (τ : X.Ψ) (a j : Fin r) : ℝ :=
  Dsg X j / Dsg X a * (v τ a - v τ j)

theorem coefR_nonneg {r : ℕ} (X : Data E r) (v : X.Ψ → Fin r → ℝ) (hv : IsDominantR X v) (τ : X.Ψ)
    (a j : Fin r) (h : (a : ℕ) < j) : 0 ≤ coefR X v τ a j := by
  obtain ⟨h1, h2, h3⟩ := hv τ
  have hle : a ≤ j := Fin.le_iff_val_le_val.mpr h.le
  have f1 := fun (hj : (j : ℕ) < X.p0) => h1 a j hle hj
  have f2 := fun (ha : X.p0 ≤ (a : ℕ)) => h2 a j ha hle
  have f3 := fun (ha : (a : ℕ) < X.p0) (hj : X.p0 ≤ (j : ℕ)) => h3 a j ha hj
  unfold coefR Dsg sgn
  split_ifs <;> first
    | (exfalso; omega)
    | (norm_num <;> (first | linarith [f1 (by omega)] | linarith [f2 (by omega)] | linarith [f3 (by omega) (by omega)]))

theorem affine_nonneg (α β t t1 : ℝ) (h0 : 0 ≤ α) (h1 : 0 ≤ α + β * t1) (ht : 0 ≤ t) (ht1 : t ≤ t1) :
    0 ≤ α + β * t := by
  rcases le_total 0 β with hb | hb
  · nlinarith [mul_nonneg hb ht]
  · nlinarith [mul_le_mul_of_nonpos_left ht1 hb]

theorem curvNumStatement_holds : CurvNumStatement (E := E) := by
  intro r X L de Fp T rr η hη hrr hT hL hLde hdom
  refine ⟨fun x0 _ z hz ξ hξ => (curvature_statement_holds r X L x0 z hz).2 hL ξ hξ,
    fun x0 _ z hz ξ hξ => (curvature_statement_holds r X (2 • L - de) x0 z hz).2 hLde ξ hξ, ?_⟩
  intro t ht htT x0 _ z hz ξ
  obtain ⟨b, hb, hgr⟩ := MajorantNormalForms.exists_normal_frame X hz
  have hgram : ∀ τ, gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) =
      diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := fun τ => (hgr τ).1
  set v : X.Ψ → Fin r → ℝ := fun τ a =>
    ((Fp - kapW X - nd X • L) τ a : ℝ) - t * (rr / 2) * (de τ a : ℝ) - 2 * η * (L τ a : ℝ) with hv

  have ht1 : t ≤ 2 * T / rr := by rw [le_div_iff₀ hrr]; linarith
  have hv0 := hdom 0 (by simp)
  have hv1 := hdom (2 * T / rr) (by simp)
  have hvt : IsDominantR X v := by
    intro τ
    obtain ⟨a0, b0, c0⟩ := hv0 τ
    obtain ⟨a1, b1, c1⟩ := hv1 τ
    have gen : ∀ i j : Fin r,
        (fun τ a => ((Fp - kapW X - nd X • L) τ a : ℝ) - 0 * (rr / 2) * (de τ a : ℝ) - 2 * η * (L τ a : ℝ)) τ j ≤
          (fun τ a => ((Fp - kapW X - nd X • L) τ a : ℝ) - 0 * (rr / 2) * (de τ a : ℝ) - 2 * η * (L τ a : ℝ)) τ i →
        (fun τ a => ((Fp - kapW X - nd X • L) τ a : ℝ) - 2 * T / rr * (rr / 2) * (de τ a : ℝ) -
          2 * η * (L τ a : ℝ)) τ j ≤
          (fun τ a => ((Fp - kapW X - nd X • L) τ a : ℝ) - 2 * T / rr * (rr / 2) * (de τ a : ℝ) -
            2 * η * (L τ a : ℝ)) τ i → v τ j ≤ v τ i := by
      intro i j e0 e1
      simp only at e0 e1
      simp only [hv]
      have h := affine_nonneg
        ((((Fp - kapW X - nd X • L) τ i : ℝ) - 2 * η * (L τ i : ℝ)) -
          (((Fp - kapW X - nd X • L) τ j : ℝ) - 2 * η * (L τ j : ℝ)))
        (-(rr / 2) * ((de τ i : ℝ) - de τ j)) t (2 * T / rr) (by linarith) (by linarith) ht ht1
      linarith
    exact ⟨fun i j hij hj => gen i j (a0 i j hij hj) (a1 i j hij hj),
      fun i j hi hij => gen i j (b0 i j hi hij) (b1 i j hi hij),
      fun i j hi hj => gen j i (c0 i j hi hj) (c1 i j hi hj)⟩
  unfold leviM phla
  rw [levi_formula X L x0 z hz b hb hgram ξ, levi_formula X (Fp - kapW X - nd X • L) x0 z hz b hb hgram ξ,
    levi_formula X de x0 z hz b hb hgram ξ]
  rw [← sub_nonneg]
  have key : (∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
        coef X (Fp - kapW X - nd X • L) τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0) -
      t * (rr / 2) * (∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
        coef X de τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0) -
      2 * η * (∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
        coef X L τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0) =
      ∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
        coefR X v τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · unfold coef coefR; simp only [hv]; ring
    · ring
  have hnn : 0 ≤ ∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
      coefR X v τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0 :=
    Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ => by
      split_ifs with h
      · exact mul_nonneg (coefR_nonneg X v hvt τ a j h) (sq_nonneg _)
      · exact le_rfl
  linarith

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfD
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF

open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ComplexConjugate ComplexOrder ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem cd_nM (τ : X.Ψ) (a b : Fin r) : ContDiff ℂ ∞ fun z : V (nd X) => nM X z τ a b := by
  show ContDiff ℂ ∞ fun z : V (nd X) => nmat X z τ a b
  unfold nmat
  by_cases h : b < a
  · simp only [dif_pos h]
    first
      | exact (EuclideanSpace.proj (𝕜 := ℂ) _).contDiff
      | fun_prop
      | exact ((EuclideanSpace.proj (𝕜 := ℂ) _).contDiff).congr fun z => rfl
  · simp only [dif_neg h]
    exact contDiff_const

theorem unipotentFrame_inv_eq_adjugate (z : V (nd X)) (τ : X.Ψ) : (n1 X z τ)⁻¹ = (n1 X z τ).adjugate := by
  have hdet : (n1 X z τ).det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · simp [n1, nM_diag]
    · intro i j hij
      have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      exact nM_upper X z τ (show Fin.castLE X.p0_le i < Fin.castLE X.p0_le j from hij')
  rw [Matrix.inv_def, hdet]
  simp

private lemma cd_det_lemma {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {k : ℕ} {M : F → Matrix (Fin k) (Fin k) ℂ}
    (h : ∀ i j, ContDiff 𝕜 ∞ fun z => M z i j) : ContDiff 𝕜 ∞ fun z => (M z).det := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

private lemma cd_adj_lemma_2 {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {k : ℕ} {M : F → Matrix (Fin k) (Fin k) ℂ}
    (h : ∀ i j, ContDiff 𝕜 ∞ fun z => M z i j) (i j : Fin k) :
    ContDiff 𝕜 ∞ fun z => (M z).adjugate i j := by
  simp only [Matrix.adjugate_apply]
  refine cd_det_lemma fun a b => ?_
  by_cases hab : a = j
  · simp only [Matrix.updateRow_apply, hab, if_true]
    exact contDiff_const
  · simp only [Matrix.updateRow_apply, hab, if_false]
    exact h a b

theorem cd_Zt (τ : X.Ψ) (a : Fin X.p0) (m : Fin (r - X.p0)) :
    ContDiff ℂ ∞ fun z : V (nd X) => Zt X z τ a m := by
  have hfun : (fun z : V (nd X) => Zt X z τ a m) =
      fun z => ∑ k, Wm X z τ m k * (n1 X z τ).adjugate k a := by
    funext z
    simp only [Zt, Matrix.transpose_apply, Matrix.mul_apply, unipotentFrame_inv_eq_adjugate]
  rw [hfun]
  refine ContDiff.sum fun k _ => ContDiff.mul ?_ ?_
  · show ContDiff ℂ ∞ fun z : V (nd X) => nM X z τ (qI X m) (Fin.castLE X.p0_le k)
    exact cd_nM X τ _ _
  · refine cd_adj_lemma_2 (M := fun z : V (nd X) => n1 X z τ) (fun i j => ?_) k a
    show ContDiff ℂ ∞ fun z : V (nd X) => nM X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j)
    exact cd_nM X τ _ _

theorem cd_Am_entry (τ : X.Ψ) (a c : Fin X.p0) :
    ContDiff ℝ ∞ fun z : V (nd X) => Am X z τ a c := by
  have hZ : ∀ a m, ContDiff ℝ ∞ fun z : V (nd X) => Zt X z τ a m :=
    fun a m => (cd_Zt X τ a m).restrict_scalars ℝ
  have hfun : (fun z : V (nd X) => Am X z τ a c) = fun z =>
      (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) a c - ∑ m, Zt X z τ a m * star (Zt X z τ c m) := by
    funext z
    simp only [Am, Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hfun]
  refine contDiff_const.sub (ContDiff.sum fun m _ => (hZ a m).mul ?_)
  first
    | exact (hZ c m).star
    | exact Complex.conjCLE.contDiff.comp (hZ c m)

theorem cd_detAm (τ : X.Ψ) : ContDiff ℝ ∞ fun z : V (nd X) => (Am X z τ).det := by
  exact cd_det_lemma (M := fun z : V (nd X) => Am X z τ) fun a c => cd_Am_entry X τ a c

theorem rhF_contDiffAt (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (rhF X x0) z := by
  have hfun : rhF X x0 = fun w => -∑ τ, Real.log ‖(Am X w τ).det‖ := funext (rhF_eq_sum X x0 ho)
  have hpd := (mem_OmF_iff X x0 ho z).1 hz
  rw [hfun]
  refine (ContDiffAt.sum fun τ _ => ?_).neg
  have hne : (Am X z τ).det ≠ 0 := (hpd τ).det_pos.ne'
  have h1 : ContDiffAt ℝ ∞ (fun w : V (nd X) => (Am X w τ).det) z := (cd_detAm X τ).contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun w : V (nd X) => ‖(Am X w τ).det‖) z :=
    (contDiffAt_norm ℂ hne).comp z h1
  exact h2.log (norm_ne_zero_iff.2 hne)

theorem T_cd {n : ℕ} : ContDiff ℝ ∞ fun z : V n => Real.log (1 + ‖z‖ ^ 2) := by
  exact (contDiff_const.add (contDiff_norm_sq ℂ)).log fun z => by positivity

theorem eF_contDiffAt (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (eF X x0) z := by
  exact (rhF_contDiffAt X x0 ho hz).add (T_cd (n := nd X)).contDiffAt

theorem isOpen_OmF (x0 : Frame X.Ψ r) : IsOpen (OmF X x0) := by
  have hc : Continuous fun z : V (nd X) => cpt X x0 z := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    have hfun : (fun z : V (nd X) => cpt X x0 z τ a b) = fun z => ∑ k, x0 τ a k * nM X z τ k b := by
      funext z
      have h := congrFun (congrFun (mat_cpt X x0 z τ) a) b
      simpa [mat, Matrix.mul_apply] using h
    rw [hfun]
    exact continuous_finsetSum _ fun k _ => continuous_const.mul (cd_nM X τ k b).continuous
  have hmat : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => mat x τ := fun τ =>
    continuous_pi fun a => continuous_pi fun b =>
      (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))
  have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det :=
    fun τ => (hmat τ).matrix_det
  have hdmin : ∀ τ i, Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor
    refine Continuous.matrix_det ?_
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.submatrix_apply, FD.gram, Matrix.of_apply, FD.hermC, FD.col, mat]
    fun_prop
  have hset : OmF X x0 = ⋂ τ : X.Ψ, ({z | (mat (cpt X x0 z) τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {z | 0 < psgn X.p0 i * (dmin X.Gm (cpt X x0 z) τ i).re}) := by
    ext z
    simp only [OmF, Set.mem_setOf_eq, X.mem_dom_iff, Set.mem_iInter, Set.mem_inter_iff]
  rw [hset]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun ((hdet τ).comp hc) continuous_const
  · exact isOpen_lt continuous_const
      (continuous_const.mul (Complex.continuous_re.comp ((hdmin τ i).comp hc)))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfJ
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData Finset

noncomputable section

attribute [local instance] Classical.propDecidable

lemma prod_min_range (f : ℕ → ℝ) (n : ℕ) :
    ∏ a ∈ range n, ∏ b ∈ range n, f (min a b) = (∏ i ∈ range n, (∏ k ∈ range i, f k) ^ 2) * ∏ k ∈ range n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∀ a ∈ range n, ∏ b ∈ range (n + 1), f (min a b) = (∏ b ∈ range n, f (min a b)) * f a := by
      intro a ha
      rw [prod_range_succ, min_eq_left (le_of_lt (mem_range.mp ha))]
    have h2 : ∏ b ∈ range (n + 1), f (min n b) = (∏ b ∈ range n, f b) * f n := by
      rw [prod_range_succ, min_self]
      congr 1
      exact prod_congr rfl fun b hb => by rw [min_eq_right (le_of_lt (mem_range.mp hb))]
    rw [prod_range_succ (fun a => ∏ b ∈ range (n + 1), f (min a b)) n, prod_congr rfl h1, prod_mul_distrib, ih, h2,
      prod_range_succ (fun i => (∏ k ∈ range i, f k) ^ 2) n, prod_range_succ f n]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma upper_mul_diag {A B : Matrix (Fin r) (Fin r) ℂ} (hA : A.BlockTriangular id) (hB : B.BlockTriangular id)
    (k : Fin r) : (A * B) k k = A k k * B k k := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · intro j _ hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

lemma bOf_diag (y : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : mat (bOf X y) τ k k = sOf X y τ k := by
  have h1 : mat (bOf X y) τ k k = uOf X y τ k k * sOf X y τ k := by
    show (uOf X y τ * Matrix.diagonal (sOf X y τ)) k k = _
    rw [Matrix.mul_diagonal]
  rw [h1]
  have h2 : uOf X y τ k k = 1 := by
    show uMat _ k k = 1
    unfold uMat
    simp
  rw [h2, one_mul]

lemma normSq_β0_diag {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    Complex.normSq (β0 X y τ k k) = |(dOf X y τ k).re| := by
  have hinv : β0 X y τ * mat (bOf X y) τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (bOf_det X hy τ))
  have h1 := congrFun (congrFun hinv k) k
  rw [upper_mul_diag (β0_upper X hy τ) (upper_of_bor X (bOf_mem X hy) τ), bOf_diag, Matrix.one_apply_eq] at h1
  have hpos := abs_re_pos X hy τ k
  have hs : Complex.normSq (sOf X y τ k) = |(dOf X y τ k).re|⁻¹ := by
    rw [sOf, Complex.normSq_ofReal, ← pow_two, inv_pow, Real.sq_sqrt (abs_nonneg _)]
  have h2 := congrArg Complex.normSq h1
  rw [Complex.normSq_mul, hs, map_one] at h2
  field_simp at h2
  linarith

def δ (y : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : ℝ := |(dOf X y τ k).re|

def fδ (y : Frame X.Ψ r) (τ : X.Ψ) (k : ℕ) : ℝ := if h : k < r then δ X y τ ⟨k, h⟩ else 1

lemma normSq_det_jac {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    Complex.normSq (LinearMap.det (Lβ (β0 X y))) * Complex.normSq (jacβ (β0 X y)) =
      ∏ i : Ix X.Ψ r, δ X y i.1 (min i.2.1 i.2.2) := by
  rw [det_Lβ _ (β0_upper X hy), jacβ, map_prod, map_prod]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Ix X.Ψ r => i.2.2 < i.2.1)
    (fun i => δ X y i.1 (min i.2.1 i.2.2))]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Ix X.Ψ r => i.2.2 < i.2.1)
    (fun i => Complex.normSq (if i.2.2 < i.2.1 then β0 X y i.1 i.2.2 i.2.2 else 1))]
  have e1 : ∏ i : UpI X.Ψ r, Complex.normSq (β0 X y i.1.1 i.1.2.1 i.1.2.1) =
      ∏ i : {i : Ix X.Ψ r // ¬ i.2.2 < i.2.1}, δ X y i.1.1 (min i.1.2.1 i.1.2.2) :=
    Finset.prod_congr rfl fun i _ => by rw [normSq_β0_diag X hy, min_eq_left (not_lt.1 i.2)]; rfl
  have e2 : ∏ i : {i : Ix X.Ψ r // ¬ i.2.2 < i.2.1},
      Complex.normSq (if i.1.2.2 < i.1.2.1 then β0 X y i.1.1 i.1.2.2 i.1.2.2 else 1) = 1 :=
    Finset.prod_eq_one fun i _ => by rw [if_neg i.2, map_one]
  have e3 : ∏ i : {i : Ix X.Ψ r // i.2.2 < i.2.1},
      Complex.normSq (if i.1.2.2 < i.1.2.1 then β0 X y i.1.1 i.1.2.2 i.1.2.2 else 1) =
      ∏ i : {i : Ix X.Ψ r // i.2.2 < i.2.1}, δ X y i.1.1 (min i.1.2.1 i.1.2.2) :=
    Finset.prod_congr rfl fun i _ => by rw [if_pos i.2, normSq_β0_diag X hy, min_eq_right i.2.le]; rfl
  rw [e1, e2, e3, mul_one, mul_comm]

lemma norm_dmin {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm y τ i‖ = ∏ k ∈ range i, fδ X y τ k := by
  rw [dmin_prod X hy τ i, norm_prod, ← Fin.prod_univ_eq_prod_range (fδ X y τ)]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj : (j : ℕ) < r := lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ i.isLt)
  rw [fδ, dite_eq_left hj, δ]
  have hre := dOf_real X hy τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
  have hc : Fin.castLE (Nat.le_of_lt_succ i.isLt) j = (⟨j, hj⟩ : Fin r) := Fin.ext rfl
  rw [hc] at hre ⊢
  exact (Complex.abs_re_eq_norm.2 hre).symm

theorem exponent_identity {y : Frame X.Ψ r} (hy : y ∈ X.dom) (hlast : ∀ τ, ‖dmin X.Gm y τ (Fin.last r)‖ = 1) :
    Complex.normSq (LinearMap.det (Lβ (β0 X y))) * Complex.normSq (jacβ (β0 X y)) =
      ∏ τ, ∏ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ ^ 2 := by
  have hτ : ∀ τ : X.Ψ, ∏ a : Fin r, ∏ b : Fin r, δ X y τ (min a b) =
      ∏ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ ^ 2 := by
    intro τ
    have hp := prod_min_range (fδ X y τ) r
    have hl : ∏ k ∈ range r, fδ X y τ k = 1 := by
      have h1 := norm_dmin X hy τ (Fin.last r)
      rw [hlast τ, Fin.val_last] at h1
      exact h1.symm
    rw [hl, mul_one] at hp
    have hd : ∀ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ = ∏ k ∈ range (i : ℕ), fδ X y τ k := by
      intro i
      rw [norm_dmin X hy τ i.castSucc, Fin.coe_castSucc]
    have e1 : ∀ a b : Fin r, δ X y τ (min a b) = fδ X y τ (min (a : ℕ) (b : ℕ)) := by
      intro a b
      unfold fδ
      rw [dite_eq_left (min_lt_of_left_lt a.isLt)]
      congr 1
    simp only [hd, e1]
    simp only [Finset.prod_range] at hp ⊢
    exact hp
  rw [normSq_det_jac X hy]
  unfold Ix
  simp only [Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun τ _ => hτ τ

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

