module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FrameMeasStatementPfB
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM

open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem Umat_upper (y : UpI X.Ψ r → ℂ) (τ : X.Ψ) : (Umat y τ).BlockTriangular id := by
  intro a b hab
  have h : b < a := hab
  simp [Umat, h]

theorem Lβ_bound {C : Set (Frame X.Ψ r)} (hCd : C ⊆ X.dom) {R0 : ℝ}
    (hR0 : ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ R0) {p : Frame X.Ψ r} (hp : p ∈ X.dom)
    {y : UpI X.Ψ r → ℂ} (hy : ∀ τ b, y (dI τ b) ≠ 0) (hx : rmul p (UF X y) ∈ C) (i : UpI X.Ψ r) :
    ‖Lβ (β0 X p) y i‖ ≤ R0 := by
  set x := rmul p (UF X y) with hxdef
  set τ := i.1.1
  have hxd : x ∈ X.dom := hCd hx
  have h1 : gram τ.1 X.Gm (mat x τ) = gramT X (β0 X p τ * mat (UF X y) τ) := gram_rmul_eq X hp τ
  let one : Frame X.Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)
  have hone' : rmul x one = x := by
    funext τ'
    show (mat x τ' * (1 : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = x τ'
    rw [Matrix.mul_one]; rfl
  have h2 : gram τ.1 X.Gm (mat x τ) = gramT X (β0 X x τ * mat one τ) := by
    have := gram_rmul_eq X hxd τ (b := one)
    rwa [hone'] at this
  have hone : mat one τ = 1 := rfl
  rw [hone, Matrix.mul_one] at h2
  have hU : mat (UF X y) τ = Umat y τ := rfl
  rw [hU] at h1
  have hUd : (Umat y τ).det ≠ 0 := ((UF_mem X hy) τ).1
  obtain ⟨D, hD, heq⟩ := gram_upper_unique (ε := fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (fun a => sgn_mul_self X.p0 a) (β0_upper X hxd τ) ((β0_upper X hp τ).mul (Umat_upper X y τ))
    (β0_det X hxd τ) (by rw [Matrix.det_mul]; exact mul_ne_zero (β0_det X hp τ) hUd)
    (by have := h1.symm.trans h2; simpa only [gramT, Jd] using this)
  have hval : Lβ (β0 X p) y i = (β0 X p τ * Umat y τ) i.1.2.1 i.1.2.2 := rfl
  rw [hval, heq, Matrix.diagonal_mul, norm_mul, hD, one_mul]
  exact hR0 x hx τ _ _

def SR (R0 : ℝ) : Set (UpI X.Ψ r → ℂ) := {c | ∀ i, ‖c i‖ ≤ R0}

def KR (R0 : ℝ) : ℝ≥0∞ := ∫⁻ y in SR X R0, ENNReal.ofReal (Complex.normSq (jacU y))

theorem measurableSet_SR (R0 : ℝ) : MeasurableSet (SR X R0) := by
  have h : SR X R0 = ⋂ i, {c : UpI X.Ψ r → ℂ | ‖c i‖ ≤ R0} := by
    ext c
    simp [SR]
  rw [h]
  exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i).norm measurable_const

theorem KR_lt_top {R0 : ℝ} (hR0 : 0 ≤ R0) : KR X R0 < ⊤ := by
  have hc : IsCompact (SR X R0) := by
    have h : SR X R0 = Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℂ) R0) := by
      ext c
      simp [SR, Set.mem_pi]
    rw [h]
    exact isCompact_univ_pi fun _ => isCompact_closedBall 0 R0
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn
    ((Complex.continuous_normSq.comp continuous_jacU).continuousOn)
  calc KR X R0 ≤ ∫⁻ _ in SR X R0, ENNReal.ofReal C := by
        unfold KR
        refine setLIntegral_mono measurable_const fun y hy => ENNReal.ofReal_le_ofReal ?_
        have := hC y hy
        rw [Real.norm_eq_abs] at this
        exact le_trans (le_abs_self _) this
    _ = ENNReal.ofReal C * volume (SR X R0) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hc.measure_lt_top

theorem upper_gen (β : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id)
    (hd : ∀ τ b, β τ b b ≠ 0) (R0 : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (SR X R0).indicator 1 (Lβ β y) =
      ENNReal.ofReal ((Complex.normSq (LinearMap.det (Lβ β)) * Complex.normSq (jacβ β))⁻¹) * KR X R0 := by
  have hdet : LinearMap.det (Lβ β) ≠ 0 := det_Lβ_ne β hβ hd
  have hjac : jacβ β ≠ 0 := by
    unfold jacβ
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    split_ifs
    · exact hd _ _
    · exact one_ne_zero
  have hnj : 0 < Complex.normSq (jacβ β) := Complex.normSq_pos.2 hjac
  have hnd : 0 < Complex.normSq (LinearMap.det (Lβ β)) := Complex.normSq_pos.2 hdet
  let Lr : (UpI X.Ψ r → ℂ) →ₗ[ℝ] (UpI X.Ψ r → ℂ) := (Lβ β).restrictScalars ℝ
  have hdetr : LinearMap.det Lr = Complex.normSq (LinearMap.det (Lβ β)) := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  have hdetr0 : LinearMap.det Lr ≠ 0 := by rw [hdetr]; exact hnd.ne'
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (UpI X.Ψ r → ℂ)) hdetr0
  have hSm : MeasurableSet (SR X R0) := measurableSet_SR X R0
  let c : ℝ≥0∞ := ENNReal.ofReal ((Complex.normSq (jacβ β))⁻¹)
  let G : (UpI X.Ψ r → ℂ) → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (Complex.normSq (jacU u)) * c * (SR X R0).indicator 1 u
  have hG : Measurable G :=
    (measurable_normSq_jacU.mul_const c).mul (measurable_one.indicator hSm)
  have hLm : Measurable Lr := Lr.continuous_of_finiteDimensional.measurable
  have hpt : ∀ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (SR X R0).indicator 1 (Lβ β y) =
      G (Lr y) := by
    intro y
    have e : ENNReal.ofReal (Complex.normSq (jacβ β * jacU y)) * c =
        ENNReal.ofReal (Complex.normSq (jacU y)) := by
      rw [Complex.normSq_mul, ← ENNReal.ofReal_mul (mul_nonneg hnj.le (Complex.normSq_nonneg _))]
      congr 1
      rw [mul_right_comm, mul_inv_cancel₀ hnj.ne', one_mul]
    show _ = ENNReal.ofReal (Complex.normSq (jacU (Lβ β y))) * c * (SR X R0).indicator 1 (Lβ β y)
    rw [jacU_Lβ β hβ y, e]
  have hGi : ∫⁻ u, G u = KR X R0 * c := by
    have h : G = (SR X R0).indicator (fun u => ENNReal.ofReal (Complex.normSq (jacU u)) * c) := by
      funext u
      simp only [G, Set.indicator]
      split_ifs <;> simp
    rw [h, lintegral_indicator hSm, lintegral_mul_const _ measurable_normSq_jacU]
    rfl
  calc ∫⁻ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (SR X R0).indicator 1 (Lβ β y)
      = ∫⁻ y, G (Lr y) := lintegral_congr fun y => hpt y
    _ = ∫⁻ u, G u ∂(Measure.map Lr volume) := (lintegral_map hG hLm).symm
    _ = ENNReal.ofReal |(LinearMap.det Lr)⁻¹| * ∫⁻ u, G u := by
        rw [hmap, lintegral_smul_measure, smul_eq_mul]
    _ = _ := by
        rw [hGi, hdetr, abs_of_pos (inv_pos.2 hnd), mul_inv, ENNReal.ofReal_mul (inv_pos.2 hnd).le]
        ring

def Jp (C : Set (Frame X.Ψ r)) (p : Frame X.Ψ r) : ℝ≥0∞ :=
  ∫⁻ y, (if ∀ τ b, y (dI τ b) ≠ 0 then
    ENNReal.ofReal (Complex.normSq (jacU y)) * C.indicator 1 (rmul p (UF X y)) else 0)

theorem Jp_le {C : Set (Frame X.Ψ r)} (hCd : C ⊆ X.dom) {R0 : ℝ}
    (hR0 : ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ R0) {p : Frame X.Ψ r} (hp : p ∈ X.dom)
    (hlast : ∀ τ, ‖dmin X.Gm p τ (Fin.last r)‖ = 1) :
    Jp X C p ≤ ENNReal.ofReal (densY X p) * KR X R0 := by
  have hdg : ∀ τ b, β0 X p τ b b ≠ 0 := by
    intro τ b
    have h := β0_det X hp τ
    rw [Matrix.det_of_upperTriangular (β0_upper X hp τ)] at h
    exact Finset.prod_ne_zero_iff.1 h b (Finset.mem_univ b)
  have hle : Jp X C p ≤ ∫⁻ y, ENNReal.ofReal (Complex.normSq (jacU y)) *
      (SR X R0).indicator 1 (Lβ (β0 X p) y) := by
    unfold Jp
    refine lintegral_mono fun y => ?_
    split_ifs with hy
    · by_cases hx : rmul p (UF X y) ∈ C
      · have hS : Lβ (β0 X p) y ∈ SR X R0 := fun i => Lβ_bound X hCd hR0 hp hy hx i
        simp [Set.indicator_of_mem hx, Set.indicator_of_mem hS]
      · simp [Set.indicator, hx]
    · simp
  rw [upper_gen X (β0 X p) (β0_upper X hp) hdg R0, exponent_identity X hp hlast, ← densY_eq X] at hle
  exact hle

end
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfF
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Filter Complex
open scoped ContDiff ComplexConjugate

noncomputable section

variable {n : ℕ}

def bumpE (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : V n) := ⟨ε, 2 * ε, hε, by linarith⟩

def cut (ε : ℝ) (hε : 0 < ε) (y : V n) : ℂ := ((bumpE ε hε : V n → ℝ) y : ℂ)

theorem cut_contDiff (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ ∞ (cut (n := n) ε hε) :=
  Complex.ofRealCLM.contDiff.comp (bumpE ε hε).contDiff

theorem cut_one (ε : ℝ) (hε : 0 < ε) {y : V n} (hy : ‖y‖ ≤ ε) : cut ε hε y = 1 := by
  unfold cut
  rw [(bumpE ε hε).one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hy)]
  simp

theorem cut_zero (ε : ℝ) (hε : 0 < ε) {y : V n} (hy : 2 * ε ≤ ‖y‖) : cut ε hε y = 0 := by
  unfold cut
  rw [(bumpE ε hε).zero_of_le_dist (by rw [dist_zero_right]; exact hy)]
  simp

theorem wdb_cut_zero (ε : ℝ) (hε : 0 < ε) (j : Fin n) {y : V n}
    (hy : ‖y‖ < ε ∨ 2 * ε < ‖y‖) : wdb n j (cut ε hε) y = 0 := by
  have key : ∀ c : ℂ, (cut ε hε =ᶠ[𝓝 y] fun _ => c) → wdb n j (cut ε hε) y = 0 := by
    intro c hc
    unfold wdb
    rw [hc.fderiv_eq]
    simp
  rcases hy with hy | hy
  · apply key 1
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hy] with z hz
    exact cut_one ε hε (le_of_lt hz)
  · apply key 0
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact cut_zero ε hε (le_of_lt hz)

theorem wdb_cut_continuous (ε : ℝ) (hε : 0 < ε) (j : Fin n) :
    Continuous (wdb n j (cut ε hε)) := by
  have hc : Continuous (fderiv ℝ (cut (n := n) ε hε)) :=
    (cut_contDiff ε hε).continuous_fderiv (by simp)
  unfold wdb
  exact ((hc.clm_apply continuous_const).add
    (continuous_const.mul (hc.clm_apply continuous_const))).div_const 2

theorem wdb_cut_bdd (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : V n, ∑ j, ‖wdb n j (cut ε hε) y‖ ^ 2 ≤ M := by
  have hcont : Continuous (fun y : V n => ∑ j, ‖wdb n j (cut ε hε) y‖ ^ 2) :=
    continuous_finsetSum _ fun j _ => ((wdb_cut_continuous ε hε j).norm).pow 2
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : V n) (2 * ε)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : ‖y‖ ≤ 2 * ε
  · have h1 := hC y (mem_closedBall_zero_iff.mpr hy)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => by positivity)] at h1
    exact h1.trans (le_max_left _ _)
  · push_neg at hy
    have h0 : ∀ j, wdb n j (cut ε hε) y = 0 := fun j => wdb_cut_zero ε hε j (Or.inr hy)
    simp [h0]

theorem norm_pair_sq_le (a ξ : Fin n → ℂ) :
    ‖∑ j, a j * conj (ξ j)‖ ^ 2 ≤ (∑ j, ‖a j‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 := by
  have h1 : ‖∑ j, a j * conj (ξ j)‖ ≤ ∑ j, ‖a j‖ * ‖ξ j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    simp [norm_mul]
  calc ‖∑ j, a j * conj (ξ j)‖ ^ 2 ≤ (∑ j, ‖a j‖ * ‖ξ j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')

def Φ (z : V (nd X)) : V (nd X) := D.zOf (cpt X (rmul x1' b1) z)

def β (z : V (nd X)) : Frame X.Ψ r := D.bOf (cpt X (rmul x1' b1) z)

theorem cell_zero (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) :
    cpt X (rmul x1' b1) 0 ∈ ExtFPf.cell D := by
  have h0 : cpt X (rmul x1' b1) 0 = rmul x1' b1 := by
    funext τ
    show (mat (rmul x1' b1) τ * mat (nmat X 0) τ : Matrix (Fin r) (Fin r) ℂ) = rmul x1' b1 τ
    rw [IW.nmat_zero, Matrix.mul_one]
    rfl
  have hx0 : cpt X x1' 0 = x1' := by
    funext τ
    show (mat x1' τ * mat (nmat X 0) τ : Matrix (Fin r) (Fin r) ℂ) = x1' τ
    rw [IW.nmat_zero, Matrix.mul_one]
    rfl
  have hdom : x1' ∈ X.dom := IW.orth_mem_dom X x1' ho'
  have hO : (0 : V (nd X)) ∈ OmF X x1' := by
    show cpt X x1' 0 ∈ X.dom
    rw [hx0]
    exact hdom
  have hu := (D.uniq 0 hO b1 hb1).1
  rw [hx0] at hu
  rw [h0]
  exact ⟨OntoS.dom_rmul X hdom hb1, hu⟩

theorem exists_ball (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) :
    ∃ ρ1 : ℝ, 0 < ρ1 ∧ ∀ z ∈ Metric.ball (0 : V (nd X)) ρ1, cpt X (rmul x1' b1) z ∈ ExtFPf.cell D := by
  have hopen : IsOpen {z : V (nd X) | cpt X (rmul x1' b1) z ∈ ExtFPf.cell D} := by
    have h1 := ExF.isOpen_OmF (X := X) (rmul x1' b1)
    have h2 : IsOpen {z : V (nd X) | D.Δ (cpt X (rmul x1' b1) z) ≠ 0} :=
      isOpen_ne_fun (D.hΔ.continuous.comp (MI.continuous_cpt (X := X) _)) continuous_const
    exact h1.inter h2
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen 0 (cell_zero X b1 D ho' hb1)
  exact ⟨ρ, hρ, fun z hz => hball hz⟩

theorem split {z : V (nd X)} (hz : cpt X (rmul x1' b1) z ∈ ExtFPf.cell D) :
    Φ X b1 D z ∈ OmF X x1' ∧ β X b1 D z ∈ Bor X.Ψ r ∧
      cpt X (rmul x1' b1) z = rmul (cpt X x1' (Φ X b1 D z)) (β X b1 D z) :=
  D.split _ hz.1 hz.2

private theorem eq_of_unipotent_lower_mul_eq_upper {n : ℕ} (A C B1 B2 N1 N2 : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A.det)
    (hB1 : IsUnit B1.det) (hB2 : IsUnit B2.det) (hB1t : B1.BlockTriangular id) (hB2t : B2.BlockTriangular id)
    (hN1t : N1.BlockTriangular OrderDual.toDual) (hN2t : N2.BlockTriangular OrderDual.toDual)
    (hd1 : ∀ a, N1 a a = 1) (hd2 : ∀ a, N2 a a = 1) (h1 : A * N1 = C * B1) (h2 : A * N2 = C * B2) :
    N1 = N2 := by
  have hN2u : IsUnit N2.det := by
    rw [Matrix.det_of_lowerTriangular N2 hN2t]
    simp [hd2]
  have h3 : N1 * B1⁻¹ = N2 * B2⁻¹ := by
    have e : A * (N1 * B1⁻¹) = A * (N2 * B2⁻¹) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB1,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB2]
    have e' := congrArg (fun M => A⁻¹ * M) e
    rwa [Matrix.nonsing_inv_mul_cancel_left _ _ hA, Matrix.nonsing_inv_mul_cancel_left _ _ hA] at e'
  have hk : N2⁻¹ * N1 = B2⁻¹ * B1 := by
    have e3 : N1 = N1 * B1⁻¹ * B1 := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB1, Matrix.mul_one]
    rw [e3, h3, Matrix.mul_assoc N2, ← Matrix.mul_assoc N2⁻¹, Matrix.nonsing_inv_mul _ hN2u, Matrix.one_mul]
  have hPlow : (N2⁻¹ * N1).BlockTriangular OrderDual.toDual := by
    haveI := Matrix.invertibleOfIsUnitDet N2 hN2u
    exact (Matrix.blockTriangular_inv_of_blockTriangular hN2t).mul hN1t
  have hPup : (N2⁻¹ * N1).BlockTriangular id := by
    haveI := Matrix.invertibleOfIsUnitDet B2 hB2
    rw [hk]
    exact (Matrix.blockTriangular_inv_of_blockTriangular hB2t).mul hB1t
  have hoff : ∀ a c, a ≠ c → (N2⁻¹ * N1) a c = 0 := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h | h
    · exact hPlow (show OrderDual.toDual c < OrderDual.toDual a from h)
    · exact hPup h
  have hN1 : N1 = N2 * (N2⁻¹ * N1) := (Matrix.mul_nonsing_inv_cancel_left N2 N1 hN2u).symm
  have hsum : ∀ a c, (N2 * (N2⁻¹ * N1)) a c = N2 a c * (N2⁻¹ * N1) c c := by
    intro a c
    rw [Matrix.mul_apply, Finset.sum_eq_single c (fun k _ hk => by rw [hoff k c hk, mul_zero]) (by simp)]
  have hPd : ∀ c, (N2⁻¹ * N1) c c = 1 := by
    intro c
    have e := congrFun (congrFun hN1 c) c
    rw [hsum, hd1, hd2, one_mul] at e
    exact e.symm
  ext a c
  have e := congrFun (congrFun hN1 a) c
  rw [hsum, hPd, mul_one] at e
  exact e

theorem Φ_injOn (hx1 : rmul x1' b1 ∈ X.dom) :
    Set.InjOn (Φ X b1 D) {z | cpt X (rmul x1' b1) z ∈ ExtFPf.cell D} := by
  intro z1 hz1 z2 hz2 hΦ
  obtain ⟨-, hB1, e1⟩ := split X b1 D hz1
  obtain ⟨-, hB2, e2⟩ := split X b1 D hz2
  rw [hΦ] at e1
  have hlow : ∀ (z : V (nd X)) (τ : X.Ψ), (mat (nmat X z) τ).BlockTriangular OrderDual.toDual := by
    intro z τ a c hac
    have hac' : a < c := hac
    simp [mat, nmat, not_lt.2 hac'.le, hac'.ne]
  have hdiag : ∀ (z : V (nd X)) (τ : X.Ψ) (a : Fin r), mat (nmat X z) τ a a = 1 := by
    intro z τ a
    simp [mat, nmat]
  have hup : ∀ b ∈ Bor X.Ψ r, ∀ τ : X.Ψ, (mat b τ).BlockTriangular id := by
    intro b hb τ a c hac
    exact (hb τ).2 a c hac
  have hN : ∀ τ, mat (nmat X z1) τ = mat (nmat X z2) τ := by
    intro τ
    exact eq_of_unipotent_lower_mul_eq_upper (mat (rmul x1' b1) τ) (mat (cpt X x1' (Φ X b1 D z2)) τ) (mat (β X b1 D z1) τ)
      (mat (β X b1 D z2) τ) _ _ (isUnit_iff_ne_zero.2 (hx1 τ).1) (isUnit_iff_ne_zero.2 (hB1 τ).1)
      (isUnit_iff_ne_zero.2 (hB2 τ).1) (hup _ hB1 τ) (hup _ hB2 τ) (hlow z1 τ) (hlow z2 τ)
      (hdiag z1 τ) (hdiag z2 τ) (congrFun e1 τ) (congrFun e2 τ)
  ext i
  obtain ⟨⟨τ, ⟨⟨a, c⟩, hac⟩⟩, rfl⟩ : ∃ e : Ent X, Fintype.equivFin (Ent X) e = i :=
    ⟨(Fintype.equivFin (Ent X)).symm i, (Fintype.equivFin (Ent X)).apply_symm_apply i⟩
  have e := congrFun (congrFun (hN τ) a) c
  simpa [mat, nmat, hac] using e

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
end

