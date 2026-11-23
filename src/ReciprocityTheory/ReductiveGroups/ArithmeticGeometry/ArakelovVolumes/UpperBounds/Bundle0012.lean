module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0022
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfC
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD

variable {f p q N' : ℕ}

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
  | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
  | exact WithTop.coe_le_coe.mpr le_top
  | simp

theorem sqNorm_nonneg' {m : ℕ} (g : Fin m → ℂ) : 0 ≤ sqNorm g :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhF

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE

variable {f p q N' : ℕ}

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhF
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

structure LUData (X : Data E r) (x0 : Frame X.Ψ r) where
  Δ : Frame X.Ψ r → ℂ
  zOf : Frame X.Ψ r → V (nd X)
  bOf : Frame X.Ψ r → Frame X.Ψ r
  hΔ : Differentiable ℂ Δ
  dense : ∀ x ∈ X.dom, ∀ ε > 0, ∃ y ∈ Metric.ball x ε, Δ y ≠ 0
  hz : DifferentiableOn ℂ zOf {x | x ∈ X.dom ∧ Δ x ≠ 0}
  hb : DifferentiableOn ℂ bOf {x | x ∈ X.dom ∧ Δ x ≠ 0}
  split : ∀ x ∈ X.dom, Δ x ≠ 0 → zOf x ∈ OmF X x0 ∧ bOf x ∈ Bor X.Ψ r ∧
    x = rmul (cpt X x0 (zOf x)) (bOf x)
  uniq : ∀ z ∈ OmF X x0, ∀ b ∈ Bor X.Ψ r, Δ (rmul (cpt X x0 z) b) ≠ 0 ∧
    zOf (rmul (cpt X x0 z) b) = z ∧ bOf (rmul (cpt X x0 z) b) = b

theorem luData_of (hLU : LUStatement (E := E)) (X : Data E r) (x0 : Frame X.Ψ r) (hx0 : IsOrth X x0) :
    Nonempty (LUData X x0) := by
  obtain ⟨Δ, zOf, bOf, h1, h2, h3, h4, h5, h6⟩ := hLU r X x0 hx0
  exact ⟨⟨Δ, zOf, bOf, h1, h2, h3, h4, h5, h6⟩⟩

variable (X : Data E r)

def oneF : Frame X.Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)

private lemma mem_bor_iff' {Ψ : Finset (E →+* ℂ)} {b : Frame Ψ r} :
    b ∈ Bor Ψ r ↔ ∀ τ : Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 :=
  Iff.rfl

private lemma mat_rmul' {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) (τ : Ψ) :
    mat (rmul x b) τ = mat x τ * mat b τ :=
  rfl

theorem oneF_mem : oneF X ∈ Bor X.Ψ r := by
  rw [mem_bor_iff']
  intro τ
  refine ⟨?_, fun a c h => ?_⟩
  · show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp
  · show (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
    exact Matrix.one_apply_ne (ne_of_gt h)

theorem rmul_oneF (x : Frame X.Ψ r) : rmul x (oneF X) = x := by
  funext τ
  show mat x τ * (1 : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Matrix.mul_one]
  rfl

theorem rmul_assoc (x b b' : Frame X.Ψ r) : rmul (rmul x b) b' = rmul x (rmul b b') := by
  funext τ
  show mat x τ * mat b τ * mat b' τ = mat x τ * (mat b τ * mat b' τ)
  exact Matrix.mul_assoc _ _ _

theorem upper_iff (b : Frame X.Ψ r) (τ : X.Ψ) :
    (∀ a c : Fin r, c < a → b τ a c = 0) ↔ (mat b τ).BlockTriangular id := by
  exact ⟨fun h a c hca => h a c hca, fun h a c hca => h hca⟩

theorem mul_mem {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) :
    rmul b b' ∈ Bor X.Ψ r := by
  rw [mem_bor_iff']
  intro τ
  refine ⟨?_, ?_⟩
  · rw [mat_rmul', Matrix.det_mul]
    exact mul_ne_zero (mem_bor_iff'.1 hb τ).1 (mem_bor_iff'.1 hb' τ).1
  · refine (upper_iff X _ τ).2 ?_
    rw [mat_rmul']
    exact ((upper_iff X b τ).1 (mem_bor_iff'.1 hb τ).2).mul ((upper_iff X b' τ).1 (mem_bor_iff'.1 hb' τ).2)

def invF (b : Frame X.Ψ r) : Frame X.Ψ r := fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

theorem invF_mem {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : invF X b ∈ Bor X.Ψ r := by
  rw [mem_bor_iff']
  intro τ
  have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.2 (mem_bor_iff'.1 hb τ).1
  have e : mat (invF X b) τ = (mat b τ)⁻¹ := rfl
  refine ⟨?_, ?_⟩
  · rw [e]
    exact (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero
  · refine (upper_iff X _ τ).2 ?_
    rw [e]
    haveI := Matrix.invertibleOfIsUnitDet _ hu
    exact Matrix.blockTriangular_inv_of_blockTriangular ((upper_iff X b τ).1 (mem_bor_iff'.1 hb τ).2)

theorem rmul_invF {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : rmul b (invF X b) = oneF X := by
  funext τ
  show mat b τ * (mat b τ)⁻¹ = (1 : Matrix (Fin r) (Fin r) ℂ)
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (mem_bor_iff'.1 hb τ).1)

theorem diag_mul {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) (τ : X.Ψ) (i : Fin r) :
    rmul b b' τ i i = b τ i i * b' τ i i := by
  show (mat b τ * mat b' τ) i i = b τ i i * b' τ i i
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rfl
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [show mat b τ i k = 0 from (mem_bor_iff'.1 hb τ).2 i k h, zero_mul]
    · rw [show mat b' τ k i = 0 from (mem_bor_iff'.1 hb' τ).2 k i h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem bchar_mul (la : Wt X.Ψ r) {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) :
    bchar la (rmul b b') = bchar la b * bchar la b' := by
  unfold bchar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [diag_mul X hb hb' τ i, mul_zpow]

theorem bchar_oneF (la : Wt X.Ψ r) : bchar la (oneF X) = 1 := by
  simp [bchar, oneF]

variable {X} {x0 : Frame X.Ψ r} (D : LUData X x0)

def cell : Set (Frame X.Ψ r) := {x | x ∈ X.dom ∧ D.Δ x ≠ 0}

theorem cell_rmul {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hΔ : D.Δ x ≠ 0) (hb : b ∈ Bor X.Ψ r) :
    D.Δ (rmul x b) ≠ 0 ∧ D.zOf (rmul x b) = D.zOf x ∧ D.bOf (rmul x b) = rmul (D.bOf x) b := by
  obtain ⟨hz, hbx, hxe⟩ := D.split x hx hΔ
  have e : rmul x b = rmul (cpt X x0 (D.zOf x)) (rmul (D.bOf x) b) := by
    rw [← rmul_assoc X, ← hxe]
  obtain ⟨h1, h2, h3⟩ := D.uniq (D.zOf x) hz (rmul (D.bOf x) b) (mul_mem X hbx hb)
  rw [e]
  exact ⟨h1, h2, h3⟩

theorem cell_of_rmul {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r)
    (hΔ : D.Δ (rmul x b) ≠ 0) : D.Δ x ≠ 0 := by
  have hxb : rmul x b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom (X := X) hx hb
  have h := (cell_rmul D hxb hΔ (invF_mem X hb)).1
  rwa [rmul_assoc X, rmul_invF X hb, rmul_oneF X] at h

theorem cpt_cell {z : V (nd X)} (hz : z ∈ OmF X x0) :
    D.Δ (cpt X x0 z) ≠ 0 ∧ D.zOf (cpt X x0 z) = z ∧ D.bOf (cpt X x0 z) = oneF X := by
  have h := D.uniq z hz (oneF X) (oneF_mem X)
  rwa [rmul_oneF X] at h


open Classical in
def P0 (la : Wt X.Ψ r) (F : V (nd X) → ℂ) (x : Frame X.Ψ r) : ℂ :=
  if x ∈ X.dom ∧ D.Δ x ≠ 0 then bchar la (D.bOf x) * F (D.zOf x) else 0

theorem poincareLift_on_chart (la : Wt X.Ψ r) (F : V (nd X) → ℂ) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    P0 D la F (cpt X x0 z) = F z := by
  obtain ⟨h1, h2, h3⟩ := cpt_cell D hz
  have hd : cpt X x0 z ∈ X.dom := hz
  unfold P0
  rw [if_pos ⟨hd, h1⟩, h2, h3, bchar_oneF X, one_mul]

theorem poincareLift_borel_equivariant (la : Wt X.Ψ r) (F : V (nd X) → ℂ) {x b : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) : P0 D la F (rmul x b) = bchar la b * P0 D la F x := by
  have hxb : rmul x b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom (X := X) hx hb
  unfold P0
  by_cases hΔ : D.Δ x = 0
  · have hΔ' : D.Δ (rmul x b) = 0 := by
      by_contra h
      exact cell_of_rmul D hx hb h hΔ
    rw [if_neg (fun h => h.2 hΔ'), if_neg (fun h => h.2 hΔ), mul_zero]
  · obtain ⟨h1, h2, h3⟩ := cell_rmul D hx hΔ hb
    obtain ⟨-, hbx, -⟩ := D.split x hx hΔ
    rw [if_pos ⟨hxb, h1⟩, if_pos ⟨hx, hΔ⟩, h2, h3, bchar_mul X la hbx hb]
    ring

private lemma continuous_dmin' {Ψ : Finset (E →+* ℂ)} (G : Matrix (Fin r) (Fin r) E) (τ : Ψ) (i : Fin (r + 1)) :
    Continuous (fun x : Frame Ψ r => dmin G x τ i) := by
  unfold dmin lminor
  apply Continuous.matrix_det
  apply Continuous.matrix_submatrix
  refine continuous_pi (fun a => continuous_pi (fun c => ?_))
  simp only [gram, Matrix.of_apply, hermC, col, mat]
  fun_prop

private lemma isOpen_dom_upper_bounds : IsOpen X.dom := by
  show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
    ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}
  simp only [Set.setOf_forall, Set.setOf_and]
  refine isOpen_iInter_of_finite (fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite (fun i => ?_)))
  · exact isOpen_ne_fun (by unfold mat; fun_prop) continuous_const
  · exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (continuous_dmin' X.Gm τ i)))

theorem isOpen_cell : IsOpen (cell D) := by
  show IsOpen (X.dom ∩ {x | D.Δ x ≠ 0})
  exact (isOpen_dom_upper_bounds (X := X)).inter (isOpen_ne_fun D.hΔ.continuous continuous_const)

theorem diffOn_prod {ι : Type*} (u : Finset ι) {g : ι → Frame X.Ψ r → ℂ} {s : Set (Frame X.Ψ r)}
    (h : ∀ i ∈ u, DifferentiableOn ℂ (g i) s) : DifferentiableOn ℂ (fun x => ∏ i ∈ u, g i x) s := by
  classical
  revert h
  refine Finset.induction_on u (fun _ => ?_) (fun a u ha ih h => ?_)
  · simp only [Finset.prod_empty]
    exact differentiableOn_const 1
  · simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a u)).mul (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem poincareLift_differentiableOn (la : Wt X.Ψ r) (F : V (nd X) → ℂ) (hF : DifferentiableOn ℂ F (OmF X x0)) :
    DifferentiableOn ℂ (P0 D la F) (cell D) := by
  have hsub : ∀ x ∈ cell D, D.zOf x ∈ OmF X x0 ∧ D.bOf x ∈ Bor X.Ψ r := by
    intro x hx
    have hx' : x ∈ X.dom ∧ D.Δ x ≠ 0 := hx
    have h := D.split x hx'.1 hx'.2
    exact ⟨h.1, h.2.1⟩
  have hbc : DifferentiableOn ℂ (fun x => bchar la (D.bOf x)) (cell D) := by
    unfold bchar
    refine diffOn_prod (g := fun τ x => ∏ i, D.bOf x τ i i ^ la τ i) Finset.univ (fun τ _ => ?_)
    refine diffOn_prod (g := fun i x => D.bOf x τ i i ^ la τ i) Finset.univ (fun i _ => ?_)
    refine DifferentiableOn.zpow ?_ (Or.inl (fun x hx => FrameDegreeData.bdiag_ne (X := X) (hsub x hx).2 τ i))
    have h1 := (differentiableOn_pi.1 D.hb) τ
    have h2 := (differentiableOn_pi.1 h1) i
    exact (differentiableOn_pi.1 h2) i
  have hFz : DifferentiableOn ℂ (fun x => F (D.zOf x)) (cell D) :=
    hF.comp D.hz (fun x hx => (hsub x hx).1)
  refine (hbc.mul hFz).congr (fun x hx => ?_)
  have hx' : x ∈ X.dom ∧ D.Δ x ≠ 0 := hx
  unfold P0
  rw [if_pos hx']
  rfl

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfE
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Filter Complex
open scoped ContDiff ComplexConjugate Matrix

noncomputable section

variable {n : ℕ}

theorem two_le_inf : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
  | exact WithTop.coe_le_coe.mpr le_top
  | simp
  | decide
  | exact le_top

theorem levi_logNormSq_zero_at (g : V n → ℂ) (v0 : V n) (hg : ContDiffAt ℂ 2 g v0)
    (hne : g v0 ≠ 0) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((Real.log (Complex.normSq (g y)) : ℝ) : ℂ)) v0 ξ = 0 := by
  have hev1 : ∀ᶠ y in 𝓝 v0, ContDiffAt ℂ 2 g y := hg.eventually (by norm_num)
  have hev2 : ∀ᶠ y in 𝓝 v0, g y ≠ 0 := hg.continuousAt.eventually_ne hne
  have hwdb : ∀ k, wdb n k (fun y => ((Real.log (Complex.normSq (g y)) : ℝ) : ℂ)) =ᶠ[𝓝 v0]
      fun y => starRingEnd ℂ (fderiv ℂ g y (bas n k) / g y) := by
    intro k
    filter_upwards [hev1, hev2] with y hy1 hy2
    have hdg : HasFDerivAt g ((fderiv ℂ g y).restrictScalars ℝ) y :=
      ((hy1.differentiableAt (by norm_num)).hasFDerivAt).restrictScalars ℝ
    have hre : HasFDerivAt (fun w => (g w).re)
        (Complex.reCLM.comp ((fderiv ℂ g y).restrictScalars ℝ)) y :=
      Complex.reCLM.hasFDerivAt.comp y hdg
    have him : HasFDerivAt (fun w => (g w).im)
        (Complex.imCLM.comp ((fderiv ℂ g y).restrictScalars ℝ)) y :=
      Complex.imCLM.hasFDerivAt.comp y hdg
    have hN := (hre.mul hre).add (him.mul him)
    have hpos : 0 < (g y).re * (g y).re + (g y).im * (g y).im := by
      rw [← Complex.normSq_apply]
      exact Complex.normSq_pos.mpr hy2
    have hh := (Complex.ofRealCLM.hasFDerivAt.comp y (hN.log hpos.ne')).congr_of_eventuallyEq
      (f₁ := fun w => ((Real.log (Complex.normSq (g w)) : ℝ) : ℂ))
      (Filter.Eventually.of_forall fun w => by simp [Complex.normSq_apply])
    simp only [wdb]
    rw [hh.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_restrictScalars',
      Complex.reCLM_apply, Complex.imCLM_apply, Complex.ofRealCLM_apply, smul_eq_mul, map_smul]
    have hz0 : (g y).re * (g y).re + (g y).im * (g y).im ≠ 0 := hpos.ne'
    apply Complex.ext <;>
      simp [Complex.div_re, Complex.div_im, Complex.normSq_apply] <;>
      field_simp <;>
      ring
  have hgd : DifferentiableAt ℂ g v0 := hg.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℂ (fderiv ℂ g) v0 :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hwd : ∀ j k, wd n j (wdb n k (fun y => ((Real.log (Complex.normSq (g y)) : ℝ) : ℂ))) v0 = 0 := by
    intro j k
    have hφ : DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n k) / g y) v0 := by
      have hm := (hD.clm_apply (differentiableAt_const (bas n k))).mul (hgd.inv hne)
      simp only [div_eq_mul_inv]
      exact hm
    have hc : HasFDerivAt (fun y => starRingEnd ℂ (fderiv ℂ g y (bas n k) / g y))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
          ((fderiv ℂ (fun y => fderiv ℂ g y (bas n k) / g y) v0).restrictScalars ℝ)) v0 :=
      (Complex.conjCLE.hasFDerivAt.comp v0 (hφ.hasFDerivAt.restrictScalars ℝ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun w => by simp)
    simp only [wd]
    rw [(hwdb k).fderiv_eq, hc.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      map_smul, smul_eq_mul, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul,
      Complex.conj_I]
    simp [← mul_assoc, Complex.I_mul_I]
  unfold leviV
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  rw [hwd j k]
  ring

theorem normSq_contDiffAt {g : V n → ℂ} {x : V n} {k : WithTop ℕ∞} (hg : ContDiffAt ℂ k g x) :
    ContDiffAt ℝ k (fun y => Complex.normSq (g y)) x := by
  have h := ContDiffAt.norm_sq ℂ (hg.restrict_scalars ℝ)
  convert h using 1
  funext y
  exact Complex.normSq_eq_norm_sq _

def epunct (e : V n → ℝ) (g : V n → ℂ) (y : V n) : ℝ :=
  e y + (Real.log (1 + Complex.normSq (g y)) - Real.log (Complex.normSq (g y)))

variable {U : Set (V n)}

theorem isOpen_punct (hU : IsOpen U) {g : V n → ℂ} (hg : DifferentiableOn ℂ g U) :
    IsOpen {y | y ∈ U ∧ g y ≠ 0} := hg.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton

theorem contDiffAt_of_punct (hU : IsOpen U) {g : V n → ℂ} (hg : DifferentiableOn ℂ g U)
    {y : V n} (hy : y ∈ U) : ContDiffAt ℂ ∞ g y := (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n g U hU hg).contDiffAt (hU.mem_nhds hy)

theorem epunct_parts (hU : IsOpen U) {e : V n → ℝ} (he : ContDiffOn ℝ ∞ e U) {g : V n → ℂ}
    (hg : DifferentiableOn ℂ g U) {y : V n} (hy : y ∈ U) (hgy : g y ≠ 0) :
    ContDiffAt ℝ ∞ e y ∧
      ContDiffAt ℝ ∞ (fun w => Real.log (1 + Complex.normSq (g w))) y ∧
      ContDiffAt ℝ ∞ (fun w => Real.log (Complex.normSq (g w))) y := by
  have hN := normSq_contDiffAt (contDiffAt_of_punct hU hg hy)
  refine ⟨he.contDiffAt (hU.mem_nhds hy), ?_, ?_⟩
  · refine (contDiffAt_const.add hN).log ?_
    have h0 := Complex.normSq_nonneg (g y)
    have h1 : (0 : ℝ) < 1 + Complex.normSq (g y) := by linarith
    exact h1.ne'
  · exact hN.log (Complex.normSq_pos.mpr hgy).ne'

theorem epunct_smooth (hU : IsOpen U) {e : V n → ℝ} (he : ContDiffOn ℝ ∞ e U) {g : V n → ℂ}
    (hg : DifferentiableOn ℂ g U) : ContDiffOn ℝ ∞ (epunct e g) {y | y ∈ U ∧ g y ≠ 0} := by
  intro y hy
  obtain ⟨h1, h2, h3⟩ := epunct_parts hU he hg hy.1 hy.2
  exact (h1.add (h2.sub h3)).contDiffWithinAt

theorem epunct_levi (hU : IsOpen U) {e : V n → ℝ} (he : ContDiffOn ℝ ∞ e U)
    (hel : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (e w : ℂ)) y ξ).re)
    {g : V n → ℂ} (hg : DifferentiableOn ℂ g U) :
    ∀ y ∈ {y | y ∈ U ∧ g y ≠ 0}, ∀ ξ : Fin n → ℂ,
      0 ≤ (leviV n (fun w => (epunct e g w : ℂ)) y ξ).re := by
  intro y hy ξ
  have hU' := isOpen_punct hU hg
  obtain ⟨h1, h2, h3⟩ := epunct_parts hU he hg hy.1 hy.2
  have h12 := h1.of_le two_le_inf
  have h22 := h2.of_le two_le_inf
  have h32 := h3.of_le two_le_inf
  have hsplit : leviV n (fun w => (epunct e g w : ℂ)) y ξ =
      leviV n (fun w => (e w : ℂ)) y ξ +
        (leviV n (fun w => (Real.log (1 + Complex.normSq (g w)) : ℂ)) y ξ +
          (-1 : ℝ) * leviV n (fun w => (Real.log (Complex.normSq (g w)) : ℂ)) y ξ) := by
    have e1 : (fun w => (epunct e g w : ℂ)) = fun w => ((e w +
        (Real.log (1 + Complex.normSq (g w)) + (-1) * Real.log (Complex.normSq (g w))) : ℝ) : ℂ) := by
      funext w; simp only [epunct]; push_cast; ring
    rw [e1, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h12 (h22.add (contDiffAt_const.mul h32)),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_add h22 (contDiffAt_const.mul h32),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-1) h32]
  rw [hsplit, levi_logNormSq_zero_at g y ((contDiffAt_of_punct hU hg hy.1).of_le two_le_inf) hy.2 ξ]
  have hlse := lseV n 2 _ (fun i : Fin 2 => ![fun _ => Complex.normSq (1 : ℂ), fun w => Complex.normSq (g w)] i) hU'
    (fun i => Or.inr (by
      fin_cases i
      · exact ⟨fun _ => 1, contDiffOn_const, fun _ _ => rfl⟩
      · exact ⟨g, ((contDiffOn_of_differentiableOn n g U hU hg).of_le two_le_inf).mono
          (fun w hw => hw.1), fun _ _ => rfl⟩))
    (fun w _ => by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.normSq_one]
      linarith [Complex.normSq_nonneg (g w)]) y hy ξ
  have e2 : (fun w => ((Real.log (∑ i : Fin 2, ![fun _ => Complex.normSq (1 : ℂ),
      fun w => Complex.normSq (g w)] i w) : ℝ) : ℂ)) =
      fun w => ((Real.log (1 + Complex.normSq (g w)) : ℝ) : ℂ) := by
    funext w; simp [Fin.sum_univ_two]
  rw [e2] at hlse
  simp only [mul_zero, add_zero, Complex.add_re]
  exact add_nonneg (hel y hy.1 ξ) hlse

theorem log_gap_pos {N : ℝ} (hN : 0 < N) : 0 < Real.log (1 + N) - Real.log N := by
  exact sub_pos.mpr (Real.log_lt_log hN (by linarith))

theorem epunct_compact (hU : IsOpen U) {e : V n → ℝ} (he : ContDiffOn ℝ ∞ e U)
    (hec : ∀ a, IsCompact {y | y ∈ U ∧ e y ≤ a}) (he0 : ∀ y ∈ U, 0 ≤ e y)
    {g : V n → ℂ} (hg : DifferentiableOn ℂ g U) (a : ℝ) :
    IsCompact {y | y ∈ {y | y ∈ U ∧ g y ≠ 0} ∧ epunct e g y ≤ a} := by
  let K : Set (V n) := {y | y ∈ U ∧ e y ≤ a}
  let K1 : Set (V n) := K ∩ (fun y => Real.exp a * Complex.normSq (g y)) ⁻¹' Set.Ici 1
  let K2 : Set (V n) := K1 ∩ (epunct e g) ⁻¹' Set.Iic a
  have hK : IsCompact K := hec a
  have hc1 : ContinuousOn (fun y => Real.exp a * Complex.normSq (g y)) K :=
    continuousOn_const.mul
      (Complex.continuous_normSq.comp_continuousOn (hg.continuousOn.mono fun y hy => hy.1))
  have hK1 : IsClosed K1 := hc1.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici
  have hcont : ContinuousOn (epunct e g) K1 := by
    intro y hy
    have hyU : y ∈ U := hy.1.1
    have hN : Complex.normSq (g y) ≠ 0 := by
      intro h0
      have h2 : (1 : ℝ) ≤ Real.exp a * Complex.normSq (g y) := hy.2
      rw [h0, mul_zero] at h2
      linarith
    have hgc : ContinuousAt g y := (hg.differentiableAt (hU.mem_nhds hyU)).continuousAt
    have hNc : ContinuousAt (fun w => Complex.normSq (g w)) y :=
      Complex.continuous_normSq.continuousAt.comp hgc
    have hec' : ContinuousAt e y := (he.contDiffAt (hU.mem_nhds hyU)).continuousAt
    have h1 : (1 : ℝ) + Complex.normSq (g y) ≠ 0 := by
      have h0 := Complex.normSq_nonneg (g y)
      have h1 : (0 : ℝ) < 1 + Complex.normSq (g y) := by linarith
      exact h1.ne'
    exact (hec'.add (((continuousAt_const.add hNc).log h1).sub (hNc.log hN))).continuousWithinAt
  have hK2 : IsClosed K2 := hcont.preimage_isClosed_of_isClosed hK1 isClosed_Iic
  have heq : {y | y ∈ {y | y ∈ U ∧ g y ≠ 0} ∧ epunct e g y ≤ a} = K2 := by
    ext y
    constructor
    · rintro ⟨⟨hyU, hgy⟩, hya⟩
      have hNpos : 0 < Complex.normSq (g y) := Complex.normSq_pos.mpr hgy
      have hgap := log_gap_pos hNpos
      have he0y := he0 y hyU
      have hdef : epunct e g y = e y + (Real.log (1 + Complex.normSq (g y)) -
          Real.log (Complex.normSq (g y))) := rfl
      have hya' : epunct e g y ≤ a := hya
      refine ⟨⟨⟨hyU, by linarith⟩, ?_⟩, hya⟩
      show 1 ≤ Real.exp a * Complex.normSq (g y)
      have h1 : Real.log (1 + Complex.normSq (g y)) ≤ a + Real.log (Complex.normSq (g y)) := by
        linarith
      rw [Real.log_le_iff_le_exp (by linarith), Real.exp_add, Real.exp_log hNpos] at h1
      linarith
    · rintro ⟨⟨⟨hyU, -⟩, hy1⟩, hya⟩
      refine ⟨⟨hyU, ?_⟩, hya⟩
      intro h0
      have h2 : (1 : ℝ) ≤ Real.exp a * Complex.normSq (g y) := hy1
      rw [h0, Complex.normSq_zero, mul_zero] at h2
      linarith
  rw [heq]
  exact hK.of_isClosed_subset hK2 (fun y hy => hy.1.1)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
end

