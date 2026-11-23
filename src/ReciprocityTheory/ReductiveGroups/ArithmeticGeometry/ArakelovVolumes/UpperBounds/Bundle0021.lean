module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfB
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace BigB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem S_pos (X : Data E r) (Xa : ArchInM X) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
  obtain ⟨k, hk⟩ := Xa.w_nz x hx
  have hd' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  have hne : ∀ (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm x τ i ≠ 0 := by
    intro τ i h0
    have h1 := (hd' τ).2 i
    rw [h0] at h1
    simp at h1
  have hp : 0 < X.pnorm Xa.L (Xa.w k) x := by
    unfold Data.pnorm
    apply mul_pos (norm_pos_iff.mpr hk)
    apply Finset.prod_pos
    intro τ _
    apply Finset.prod_pos
    intro i _
    apply Real.rpow_pos_of_pos
    exact norm_pos_iff.mpr (div_ne_zero (hne τ i.succ) (hne τ i.castSucc))
  calc (0 : ℝ) < X.pnorm Xa.L (Xa.w k) x ^ 2 := by positivity
    _ ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 :=
      Finset.single_le_sum (f := fun k => X.pnorm Xa.L (Xa.w k) x ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ k)

theorem pnorm_contOn (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) :
    ContinuousOn (X.pnorm la P) X.dom := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor
    apply Continuous.matrix_det
    apply continuous_pi
    intro a
    apply continuous_pi
    intro b
    simp only [Matrix.submatrix_apply, gram, hermC, Matrix.of_apply, mat, col]
    fun_prop
  have hne : ∀ x ∈ X.dom, ∀ (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm x τ i ≠ 0 := by
    intro x hx τ i h0
    have hd' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
        ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
    have h1 := (hd' τ).2 i
    rw [h0] at h1
    simp at h1
  unfold Data.pnorm
  apply ContinuousOn.mul
  · exact continuous_norm.comp_continuousOn hP.1.continuousOn
  · apply continuousOn_finsetProd
    intro τ _
    apply continuousOn_finsetProd
    intro i _
    apply ContinuousOn.rpow_const
    · exact (((hd τ i.succ).continuousOn).div (hd τ i.castSucc).continuousOn
        (fun x hx => hne x hx τ i.castSucc)).norm
    · intro x hx
      left
      exact norm_ne_zero_iff.mpr (div_ne_zero (hne x hx τ i.succ) (hne x hx τ i.castSucc))

theorem r_pos (X : Data E r) (Xa : ArchInM X) : 0 < r := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · exfalso
    subst hr
    have h := Xa.n_ge
    have h0 : nd X = 0 := by
      unfold nd
      rw [Fintype.card_eq_zero_iff]
      constructor
      rintro ⟨_, ⟨⟨a, _⟩, _⟩⟩
      exact a.elim0
    omega
  · exact hr

theorem lam_ne (X : Data E r) (Xa : ArchInM X) : ∃ v ∈ X.Λ, v ≠ 0 := by
  have hr := r_pos X Xa
  by_contra h
  push_neg at h
  have h1 : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ ⊥ := by
    rw [Submodule.span_le]
    intro v hv
    simp [h v hv]
  rw [X.Λ_span, top_le_iff] at h1
  have hm : (fun _ => (1 : E) : Fin r → E) ∈ (⊤ : Submodule E (Fin r → E)) := Submodule.mem_top
  rw [← h1, Submodule.mem_bot] at hm
  exact one_ne_zero (congrFun hm ⟨0, hr⟩)

end BigB

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.EtaStatementHolds
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.EtaPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff

private lemma fderiv_const_mul_apply {n : ℕ} (t : ℝ) (g : V n → ℂ) (y : V n) (v : V n) :
    fderiv ℝ (fun w => (t : ℂ) * g w) y v = (t : ℂ) * fderiv ℝ g y v := by
  by_cases hd : DifferentiableAt ℝ g y
  · rw [fderiv_const_mul hd]
    simp
  · by_cases ht : t = 0
    · subst ht
      simp
    · have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
      have hd' : ¬ DifferentiableAt ℝ (fun w => (t : ℂ) * g w) y := by
        intro h'
        apply hd
        have h'' := h'.const_mul ((t : ℂ)⁻¹)
        simpa [← mul_assoc, inv_mul_cancel₀ ht'] using h''
      rw [fderiv_zero_of_not_differentiableAt hd', fderiv_zero_of_not_differentiableAt hd]
      simp

private lemma wd_const_mul (n : ℕ) (j : Fin n) (t : ℝ) (g : V n → ℂ) (y : V n) :
    wd n j (fun w => (t : ℂ) * g w) y = (t : ℂ) * wd n j g y := by
  unfold wd
  rw [fderiv_const_mul_apply, fderiv_const_mul_apply]
  ring

private lemma wdb_const_mul (n : ℕ) (j : Fin n) (t : ℝ) (g : V n → ℂ) :
    wdb n j (fun w => (t : ℂ) * g w) = fun y => (t : ℂ) * wdb n j g y := by
  funext y
  unfold wdb
  rw [fderiv_const_mul_apply, fderiv_const_mul_apply]
  ring

private lemma leviM_const_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (g : Frame X.Ψ r → ℝ) (t : ℝ) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) :
    leviM X (fun x => t * g x) x0 z ξ = t * leviM X g x0 z ξ := by
  unfold leviM leviV
  have h1 : (fun w => (((t * g (cpt X x0 w) : ℝ)) : ℂ)) =
      fun w => (t : ℂ) * ((g (cpt X x0 w) : ℝ) : ℂ) := by
    funext w
    push_cast
    ring
  simp only [h1, wdb_const_mul, wd_const_mul, mul_assoc, ← Finset.mul_sum, Complex.re_ofReal_mul]

theorem eta_holds {E : Type} [Field E] [NumberField E] [IsCMField E] : EtaStatement (E := E) := by
  intro r X Xa
  obtain ⟨η, hη, h⟩ := Xa.posF
  refine ⟨η, hη, fun x0 ho z hz ξ => ?_⟩
  have hx0 : x0 ∈ X.dom := IW.orth_mem_dom (X := X) (x0 := x0) (ho := ho)
  have hzd : cpt X x0 z ∈ X.dom := hz
  have hc1 := Xa.frame_theta_const_pos
  have ha1 := Xa.frame_theta_weight_pos
  have ht0 : (0 : ℝ) ≤ 1 + Xa.c1 / Xa.a1 := by positivity
  have htr : (1 + Xa.c1 / Xa.a1) * Xa.rr ≤ 2 * (Xa.T : ℝ) := by
    rw [mul_comm]
    exact Xa.rr_le
  have h1 := h (1 + Xa.c1 / Xa.a1) ht0 htr x0 hx0 z hzd ξ
  have h2 := Xa.base_psi_levi_lower_bound x0 hx0 z hzd ξ
  have h3 := IW.leviM_comb (X := X) (x0 := x0) (ho := ho) (hz := hz) (la1 := Xa.Fp) (la2 := Xa.L)
    (k := nd X) (ξ := ξ)
  have h4 := leviM_const_mul X Xa.ps0 (1 + Xa.c1 / Xa.a1) x0 z ξ
  have h5 := mul_le_mul_of_nonneg_left h2 ht0
  rw [h3] at h1
  unfold leviO at h1 ⊢
  rw [h4]
  nlinarith [h1, h5]

end ReciprocityTheory.ChartRestriction.G.AR.Up.EtaPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustGPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Topology Filter ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.FD
open scoped ContDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace ExG

theorem two_le_inf : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
    | exact WithTop.coe_le_coe.mpr le_top
    | exact (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤) : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
    | decide
    | simp
    | norm_num

variable {r : ℕ} (X : Data E r)

private lemma isOpen_omF (x0 : Frame X.Ψ r) : IsOpen (OmF X x0) := by
  first
  | exact ExF.isOpen_OmF X x0
  | exact isOpen_OmF X x0
  | exact ExF.isOpen_Om X x0
  | exact (X.isOpen_dom).preimage (continuous_cpt X x0)
  | exact X.isOpen_dom.preimage (by unfold cpt; fun_prop)
  | exact X.dom_open.preimage (by unfold cpt; fun_prop)
  | exact X.hdom.preimage (by unfold cpt; fun_prop)

theorem isOpen_Om (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0)) :
    IsOpen {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} := by
  have hO := isOpen_omF X x0
  exact hg.continuousOn.isOpen_inter_preimage hO isOpen_ne

theorem g_cd (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0))
    {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℂ ∞ g1 z := by
  exact (contDiffOn_of_differentiableOn (nd X) g1 (OmF X x0) (isOpen_omF X x0) hg).contDiffAt
    ((isOpen_omF X x0).mem_nhds hz)

theorem inv_cd (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0))
    {z : V (nd X)} (hz : z ∈ OmF X x0) (hne : g1 z ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => (‖g1 y‖ ^ 2)⁻¹) z := by
  have h1 : ContDiffAt ℝ ∞ g1 z := (g_cd X x0 g1 hg hz).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ∞ (fun y => ‖g1 y‖ ^ 2) z := (contDiff_norm_sq ℝ).contDiffAt.comp z h1
  exact h2.inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))

theorem levi_inv_nonneg (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0))
    {z : V (nd X)} (hz : z ∈ OmF X x0) (hne : g1 z ≠ 0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun y => (((‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) z ξ).re := by
  have hfun : (fun y => (((‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) = fun y => ((Complex.normSq ((g1 y)⁻¹) : ℝ) : ℂ) := by
    funext y
    rw [Complex.normSq_inv, Complex.normSq_eq_norm_sq]
  have hcd : ContDiffAt ℂ 2 (fun y => (g1 y)⁻¹) z := ((g_cd X x0 g1 hg hz).of_le two_le_inf).inv hne
  rw [hfun, leviV_normSq_comp hcd ξ, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

theorem isCompact_sub (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (g1 : V (nd X) → ℂ)
    (hg : DifferentiableOn ℂ g1 (OmF X x0)) (a : ℝ) :
    IsCompact {z : V (nd X) | (z ∈ OmF X x0 ∧ g1 z ≠ 0) ∧ eF X x0 z + (‖g1 z‖ ^ 2)⁻¹ ≤ a} := by
  have hK := ExF.isCompact_subF X x0 ho a
  have hcont : ContinuousOn (fun z => ‖g1 z‖ ^ 2 * (a - eF X x0 z)) {z | z ∈ OmF X x0 ∧ eF X x0 z ≤ a} :=
    ((hg.continuousOn.norm.pow 2).mul (continuousOn_const.sub (fun z hz =>
      (ExF.eF_contDiffAt X x0 ho hz).continuousAt.continuousWithinAt))).mono (fun z hz => hz.1)
  have hcl := hcont.preimage_isClosed_of_isClosed hK.isClosed (isClosed_Ici (a := (1 : ℝ)))
  have hset : {z : V (nd X) | (z ∈ OmF X x0 ∧ g1 z ≠ 0) ∧ eF X x0 z + (‖g1 z‖ ^ 2)⁻¹ ≤ a} =
      {z | z ∈ OmF X x0 ∧ eF X x0 z ≤ a} ∩ (fun z => ‖g1 z‖ ^ 2 * (a - eF X x0 z)) ⁻¹' Set.Ici 1 := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici]
    constructor
    · rintro ⟨⟨hzO, hz0⟩, hle⟩
      have hpos : 0 < ‖g1 z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz0) 2
      have hinv : 0 ≤ (‖g1 z‖ ^ 2)⁻¹ := inv_nonneg.mpr hpos.le
      refine ⟨⟨hzO, by linarith⟩, ?_⟩
      have hle' : (‖g1 z‖ ^ 2)⁻¹ ≤ a - eF X x0 z := by linarith
      calc (1 : ℝ) = ‖g1 z‖ ^ 2 * (‖g1 z‖ ^ 2)⁻¹ := (mul_inv_cancel₀ hpos.ne').symm
        _ ≤ ‖g1 z‖ ^ 2 * (a - eF X x0 z) := mul_le_mul_of_nonneg_left hle' hpos.le
    · rintro ⟨⟨hzO, _⟩, h1⟩
      have hz0 : g1 z ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at h1
        norm_num at h1
      have hpos : 0 < ‖g1 z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz0) 2
      refine ⟨⟨hzO, hz0⟩, ?_⟩
      have hle' : (‖g1 z‖ ^ 2)⁻¹ ≤ a - eF X x0 z := by
        calc (‖g1 z‖ ^ 2)⁻¹ = (‖g1 z‖ ^ 2)⁻¹ * 1 := (mul_one _).symm
          _ ≤ (‖g1 z‖ ^ 2)⁻¹ * (‖g1 z‖ ^ 2 * (a - eF X x0 z)) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hpos.le)
          _ = a - eF X x0 z := by field_simp
      linarith
  rw [hset]
  exact hK.of_isClosed_subset hcl Set.inter_subset_left

end ExG

private theorem leviV_ofReal_add_of_contDiffAt_two {n : ℕ} {F G : V n → ℝ} {y : V n} (hF : ContDiffAt ℝ 2 F y)
    (hG : ContDiffAt ℝ 2 G y) (ξ : Fin n → ℂ) :
    leviV n (fun v => ((F v + G v : ℝ) : ℂ)) y ξ =
      leviV n (fun v => (F v : ℂ)) y ξ + leviV n (fun v => (G v : ℂ)) y ξ := by
  have h := leviV_ofReal_sum (u := ![F, G]) (x := y) (fun i => by fin_cases i <;> simpa) ξ
  simpa [Fin.sum_univ_two] using h

theorem exhaustG_holds : ExhaustGStatement (E := E) := by
  intro r X x0 ho g1 hg
  have hU : IsOpen {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} := ExG.isOpen_Om X x0 g1 hg
  have hLH : IsLocalHomeomorph (Subtype.val : {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} → V (nd X)) :=
    hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hf : ∀ z ∈ {z | z ∈ OmF X x0 ∧ g1 z ≠ 0},
      ContDiffAt ℝ ∞ (fun z => eF X x0 z + (‖g1 z‖ ^ 2)⁻¹) z := fun z hz =>
    (ExF.eF_contDiffAt X x0 ho hz.1).add (ExG.inv_cd X x0 g1 hg hz.1 hz.2)
  refine ⟨{ z := Subtype.val
            isLocalHomeomorph := hLH
            e := fun y => eF X x0 y.1 + (‖g1 y.1‖ ^ 2)⁻¹
            smooth_e := ?_
            levi_e := ?_
            isCompact_le := ?_ }, rfl, rfl⟩
  · intro ch hch
    have hts : ∀ y ∈ ch.target, ((ch.symm y : {z | z ∈ OmF X x0 ∧ g1 z ≠ 0}) : V (nd X)) = y := fun y hy => by
      rw [hch (ch.map_target hy)]
      exact ch.right_inv hy
    have hsub : ch.target ⊆ {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} := fun y hy => by
      rw [← hts y hy]
      exact (ch.symm y).2
    have hcd : ContDiffOn ℝ ∞ (fun y => ((eF X x0 y + (‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) ch.target :=
      fun y hy => (Complex.ofRealCLM.contDiff.contDiffAt.comp y (hf y (hsub hy))).contDiffWithinAt
    refine hcd.congr (fun y hy => ?_)
    simp only [Function.comp_apply, hts y hy]
  · intro x ξ
    obtain ⟨ch, hx, hch⟩ := hLH x
    have hchart : IsChart (nd X) Subtype.val ch := fun y _ => congrFun hch y
    rw [levi_eq_leviV (nd X) Subtype.val ch hchart _ x hx ξ]
    have htg : ch.target ∈ 𝓝 (x : V (nd X)) := by
      have h0 := ch.open_target.mem_nhds (ch.map_source hx)
      rwa [← congrFun hch x] at h0
    have hgerm : (fun y => (((fun y : {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} => eF X x0 y.1 + (‖g1 y.1‖ ^ 2)⁻¹)
        (ch.symm y) : ℝ) : ℂ)) =ᶠ[𝓝 (x : V (nd X))]
        (fun y => ((eF X x0 y + (‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) := by
      filter_upwards [htg] with y hy
      have hy' : ((ch.symm y : {z | z ∈ OmF X x0 ∧ g1 z ≠ 0}) : V (nd X)) = y := by
        rw [congrFun hch (ch.symm y)]
        exact ch.right_inv hy
      simp only [hy']
    rw [leviV_congr hgerm ξ]
    have hxO : (x : V (nd X)) ∈ OmF X x0 := x.2.1
    have h2 : (2 : WithTop ℕ∞) ≤ ∞ := ExG.two_le_inf
    have hE : ContDiffAt ℝ 2 (eF X x0) x := (ExF.eF_contDiffAt X x0 ho hxO).of_le h2
    have hI : ContDiffAt ℝ 2 (fun y => (‖g1 y‖ ^ 2)⁻¹) x :=
      (ExG.inv_cd X x0 g1 hg hxO x.2.2).of_le h2
    have hR : ContDiffAt ℝ 2 (rhF X x0) x := (ExF.rhF_contDiffAt X x0 ho hxO).of_le h2
    have hT : ContDiffAt ℝ 2 (fun z : V (nd X) => Real.log (1 + ‖z‖ ^ 2)) x := ExF.T_cd.contDiffAt.of_le h2
    rw [leviV_ofReal_add_of_contDiffAt_two hE hI ξ]
    have hEsplit : leviV (nd X) (fun v => (eF X x0 v : ℂ)) x ξ =
        leviV (nd X) (fun v => (rhF X x0 v : ℂ)) x ξ +
          leviV (nd X) (fun v => (Real.log (1 + ‖v‖ ^ 2) : ℂ)) x ξ :=
      leviV_ofReal_add_of_contDiffAt_two hR hT ξ
    rw [hEsplit, Complex.add_re, Complex.add_re]
    have h1 := ExF.levi_rhF_nonneg X x0 ho hxO ξ
    have h3 := ExF.leviT_nonneg (x : V (nd X)) ξ
    have h4 := ExG.levi_inv_nonneg X x0 g1 hg hxO x.2.2 ξ
    linarith
  · intro a
    rw [Subtype.isCompact_iff]
    convert ExG.isCompact_sub X x0 ho g1 hg a using 1
    ext z
    constructor
    · rintro ⟨⟨w, hw⟩, hle, rfl⟩
      exact ⟨hw, hle⟩
    · rintro ⟨hw, hle⟩
      exact ⟨⟨z, hw⟩, hle, rfl⟩

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem countable_Γ (X : Data E r) : Countable X.Γ := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  haveI : Countable (GL (Fin r) E) := Function.Injective.countable (f := (Units.val : GL (Fin r) E → Matrix (Fin r) (Fin r) E)) (fun _ _ h => Units.ext h)
  infer_instance

def Hg (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (bb : ℝ) (φ : Frame X.Ψ r → ℝ≥0∞)
    (γ : GL (Fin r) E) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  (lact γ⁻¹ ⁻¹' Sset X x0 FF).indicator (fun y => ENNReal.ofReal (kap X x0 bb y) * φ y) x

theorem meas_Hg (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))}
    (hFF : MeasurableSet FF) (bb : ℝ) {φ : Frame X.Ψ r → ℝ≥0∞} (hφ : Measurable φ) (γ : GL (Fin r) E) :
    Measurable (Hg X x0 FF bb φ γ) :=
  ((meas_kap X x0 bb).ennreal_ofReal.mul hφ).indicator ((cont_lact X γ⁻¹).measurable (meas_S X ho hFF))

theorem Hg_rmul (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (bb : ℝ) {φ : Frame X.Ψ r → ℝ≥0∞}
    (hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) (γ : GL (Fin r) E) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    Hg X x0 FF bb φ γ (rmul x b) = Hg X x0 FF bb φ γ x := by
  classical
  simp only [Hg, Set.indicator_apply, Set.mem_preimage, lact_rmul', rmul_mem_S X hb,
    kap_rmul X x0 x bb hb, hφB x hx b hb]

private lemma lact_inv_lact_self {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact γ⁻¹ (lact γ x) = x := by
  funext τ
  have h : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * (γ : Matrix (Fin r) (Fin r) E) = 1 := by
    simp
  show ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * Matrix.of (x τ)) = x τ
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero τ.1) (map_one τ.1),
    Matrix.one_mul]
  rfl

theorem Hg_lact_cpt (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (FF : Set (V (nd X))) (bb : ℝ)
    {φ : Frame X.Ψ r → ℝ≥0∞} (hφΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, φ (lact γ x) = φ x) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    Hg X x0 FF bb φ γ (lact γ (cpt X x0 z)) =
      FF.indicator (fun z => ENNReal.ofReal (kap X x0 bb (lact γ (cpt X x0 z))) * φ (cpt X x0 z)) z := by
  classical
  rw [Hg, Set.indicator_apply, Set.mem_preimage, lact_lact, inv_mul_cancel, lact_one, cpt_mem_S X ho,
    hφΓ γ hγ _ hz, Set.indicator_apply]

theorem cover (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))} (hFF : IsFundSet X x0 FF) :
    ∀ᵐ z ∂muF X x0, ∃ γ ∈ X.Γ, lact γ⁻¹ (cpt X x0 z) ∈ Sset X x0 FF := by
  obtain ⟨-, -, -, h⟩ := hFF
  filter_upwards [h] with z hz
  obtain ⟨z', hz', γ, hγ, b, hb, he⟩ := hz
  exact ⟨γ, hγ, ⟨(z', b), ⟨hz', hb⟩, by rw [he, lact_inv_lact_self]⟩⟩

theorem kaUnfold_of (hMI : MeasInvStatement (E := E)) (hSB : SumBoundStatement) :
    KaUnfoldStatement (E := E) := by
  intro r X x0 ho hPD FF hFF bb hbb
  obtain ⟨C, hC, hCb⟩ := sum_bound hSB X ho hPD bb hbb
  have := countable_Γ X
  refine ⟨C, hC, fun φ hφ hφB hφΓ => ?_⟩
  have hae : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 := ExtFPf.ae_OmF (X := X) (x0 := x0)
  have hT := (cont_cpt X x0).measurable
  have hI : ∀ γ : X.Γ, Measurable fun z => FF.indicator
      (fun z => ENNReal.ofReal (kap X x0 bb (lact γ.1 (cpt X x0 z))) * φ (cpt X x0 z)) z := fun γ =>
    ((meas_kap X x0 bb).comp ((cont_lact X γ.1).comp (cont_cpt X x0)).measurable).ennreal_ofReal.mul
      (hφ.comp hT) |>.indicator hFF.1
  have step1 : ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * φ (cpt X x0 z) ∂muF X x0 ≤
      ∫⁻ z, ∑' γ : X.Γ, Hg X x0 FF bb φ γ.1 (cpt X x0 z) ∂muF X x0 := by
    refine lintegral_mono_ae ((hae.and (cover X hFF)).mono fun z ⟨hz, γ, hγ, hS⟩ => ?_)
    rw [kaF_eq X ho bb hz]
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (⟨γ, hγ⟩ : X.Γ))
    rw [Hg, Set.indicator_of_mem (show cpt X x0 z ∈ lact γ⁻¹ ⁻¹' Sset X x0 FF from hS)]
  have step2 : ∫⁻ z, ∑' γ : X.Γ, Hg X x0 FF bb φ γ.1 (cpt X x0 z) ∂muF X x0 =
      ∑' γ : X.Γ, ∫⁻ z, Hg X x0 FF bb φ γ.1 (cpt X x0 z) ∂muF X x0 :=
    lintegral_tsum fun γ => ((meas_Hg X ho hFF.1 bb hφ γ.1).comp hT).aemeasurable
  have step3 : ∀ γ : X.Γ, ∫⁻ z, Hg X x0 FF bb φ γ.1 (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z, FF.indicator (fun z => ENNReal.ofReal (kap X x0 bb (lact γ.1 (cpt X x0 z))) *
        φ (cpt X x0 z)) z ∂muF X x0 := by
    intro γ
    rw [hMI r X x0 (lact γ.1 x0) ho (isOrth_lact X γ.2 ho) (Hg X x0 FF bb φ γ.1)
      (meas_Hg X ho hFF.1 bb hφ γ.1) (fun x hx b hb => Hg_rmul X x0 FF bb hφB γ.1 hx hb),
      muF_lact X γ.2]
    refine lintegral_congr_ae (hae.mono fun z hz => ?_)
    show Hg X x0 FF bb φ γ.1 (cpt X (lact γ.1 x0) z) = _
    rw [cpt_lact, Hg_lact_cpt X ho FF bb hφΓ γ.2 hz]
  have step4 : ∑' γ : X.Γ, ∫⁻ z, FF.indicator (fun z => ENNReal.ofReal (kap X x0 bb (lact γ.1 (cpt X x0 z))) *
        φ (cpt X x0 z)) z ∂muF X x0 ≤ ∫⁻ z in FF, C * φ (cpt X x0 z) ∂muF X x0 := by
    rw [← lintegral_tsum fun γ => (hI γ).aemeasurable, ← lintegral_indicator hFF.1]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ FF
    · simp only [Set.indicator_of_mem hz]
      rw [ENNReal.tsum_mul_right]
      exact mul_le_mul_left (hCb z (hFF.2.1 hz)) _
    · simp [Set.indicator_of_notMem hz]
  calc ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * φ (cpt X x0 z) ∂muF X x0
      ≤ ∑' γ : X.Γ, ∫⁻ z, Hg X x0 FF bb φ γ.1 (cpt X x0 z) ∂muF X x0 := step1.trans_eq step2
    _ = ∑' γ : X.Γ, ∫⁻ z, FF.indicator (fun z => ENNReal.ofReal (kap X x0 bb (lact γ.1 (cpt X x0 z))) *
        φ (cpt X x0 z)) z ∂muF X x0 := tsum_congr step3
    _ ≤ ∫⁻ z in FF, C * φ (cpt X x0 z) ∂muF X x0 := step4
    _ = C * ∫⁻ z in FF, φ (cpt X x0 z) ∂muF X x0 := lintegral_const_mul C (hφ.comp hT)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.KU

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem kaUnfold_of (hMI : MeasInvStatement (E := E)) (hSB : SumBoundStatement) :
    KaUnfoldStatement (E := E) := KU.kaUnfold_of hMI hSB

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

