module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfH

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CurvAndMarginClosed
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.CurvMarginClosed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem curv_and_margin_closed :
    (CurvGGStatement (E := E)) ∧ (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (m : ℝ), (∀ τ (i j : Fin r), i ≤ j → (j : ℕ) < X.p0 → la τ j ≤ la τ i) → (∀ τ (i j : Fin r), X.p0 ≤ (i : ℕ) → i ≤ j → la τ j ≤ la τ i) → (∀ τ (i j : Fin r), (i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) → m ≤ (la τ j : ℝ) - (la τ i : ℝ)) → ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ) := by
  have hdiag := GlobalTheory.T.leviForm_weightMetric_orthonormal_diagonal (E := E)
  have htrans := GlobalTheory.LeviTransfer.levi_transfer (E := E) GlobalTheory.FrameMeasureClosed.kapGG_holds
    GlobalTheory.NormFactor.nfac_transform
  exact GlobalTheory.CurvMargin.curv_and_margin hdiag htrans

end GlobalTheory.CurvMarginClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EventuallySplit
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FiniteZeroOrbits

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cpt_origin {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) : cpt X x 0 = x := by
  have : nmat X 0 = ExtFPf.oneF X := by
    funext τ a b
    simp only [nmat, ExtFPf.oneF, Matrix.one_apply]
    split_ifs with h1 h2 h3
    · exact absurd h2 (ne_of_gt h1)
    · rfl
    · rfl
    · rfl
  rw [cpt, this, ExtFPf.rmul_oneF]

theorem eventually_split {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∃ z ∈ Metric.closedBall (0 : V (nd X)) δ, ∃ b ∈ Bor X.Ψ r,
      y = rmul (cpt X x z) b := by
  have hu : ∀ τ, IsUnit (mat x τ).det := fun τ => isUnit_iff_ne_zero.mpr (hx τ).1
  have hM : ∀ τ, LUPf.Mx X x x τ = 1 := fun τ => Matrix.nonsing_inv_mul _ (hu τ)
  have hΔ : LUPf.DeltaF X x x ≠ 0 := by
    have : LUPf.DeltaF X x x = 1 := by
      unfold LUPf.DeltaF
      refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun k _ => ?_
      rw [hM]
      exact LUPf.lminor_one k
    rw [this]; exact one_ne_zero
  have hL : LUPf.Lm (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
    refine (LUPf.Lm_unique 1 1 (fun k => by rw [LUPf.lminor_one]; exact one_ne_zero)
      (fun i k h => Matrix.one_apply_ne (ne_of_lt h)) (fun i => Matrix.one_apply_eq i) fun i j h => ?_).symm
    rw [Matrix.one_mul]; exact Matrix.one_apply_ne (ne_of_gt h)
  have hz0 : LUPf.zF X x x = 0 := by
    ext k
    set p := (Fintype.equivFin (Ent X)).symm k with hp
    show ((LUPf.Lm (LUPf.Mx X x x p.1))⁻¹ : Matrix (Fin r) (Fin r) ℂ) p.2.1.1 p.2.1.2 = 0
    rw [hM, hL, inv_one]
    exact Matrix.one_apply_ne (ne_of_gt p.2.2)
  have hopen : IsOpen {y | y ∈ X.dom ∧ LUPf.DeltaF X x y ≠ 0} :=
    (FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun (LUPf.Delta_diff (X := X) (x0 := x)).continuous continuous_const)
  have hn := hopen.mem_nhds (show x ∈ {y | y ∈ X.dom ∧ LUPf.DeltaF X x y ≠ 0} from ⟨hx, hΔ⟩)
  have hc : ContinuousAt (LUPf.zF X x) x :=
    (LUPf.zF_diffOn (X := X) (x0 := x)).continuousOn.continuousAt hn
  have hb : ∀ᶠ y in 𝓝 x, LUPf.zF X x y ∈ Metric.closedBall (0 : V (nd X)) δ :=
    hc.preimage_mem_nhds (by rw [hz0]; exact Metric.closedBall_mem_nhds _ hδ)
  filter_upwards [hn, hb] with y hy hyb
  refine ⟨hy.1, _, hyb, _, LUPf.bF_mem hy.1 hy.2, ?_⟩
  funext τ
  show y τ = (mat x τ * mat (nmat X (LUPf.zF X x y)) τ *
    (LUPf.Lm (LUPf.Mx X x y τ) * LUPf.Mx X x y τ) : Matrix (Fin r) (Fin r) ℂ)
  rw [LUPf.nmat_zF]
  show y τ = (mat x τ * (LUPf.Lm (LUPf.Mx X x y τ))⁻¹ * (LUPf.Lm (LUPf.Mx X x y τ) * ((mat x τ)⁻¹ * mat y τ)) :
    Matrix (Fin r) (Fin r) ℂ)
  have hL' : IsUnit (LUPf.Lm (LUPf.Mx X x y τ)).det := by rw [LUPf.Lm_det]; exact isUnit_one
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (LUPf.Lm (LUPf.Mx X x y τ))⁻¹, Matrix.nonsing_inv_mul _ hL',
    Matrix.one_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu τ), Matrix.one_mul]
  rfl

theorem isolated_of_det {n : ℕ} {f : V n → V n} (hdet : (fderiv ℂ f 0).det ≠ 0) (h0 : f 0 = 0) :
    ∃ δ > 0, ∀ y ∈ Metric.closedBall (0 : V n) δ, f y = 0 → y = 0 := by
  by_cases hd : DifferentiableAt ℂ f 0
  · exact HE.iso_zero hd.hasFDerivAt hdet h0
  · refine ⟨1, one_pos, fun y _ _ => ?_⟩
    have hk := HE.ker_bot_of_det hdet
    rw [fderiv_zero_of_not_differentiableAt hd] at hk
    have : y ∈ LinearMap.ker ((0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) := by simp
    rw [hk] at this
    exact (Submodule.mem_bot ℂ).1 this

def orbitSetoid {r : ℕ} (X : Data E r) : Setoid (Frame X.Ψ r) where
  r x y := ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul x b)
  iseqv := by
    refine ⟨fun x => ⟨1, X.Γ.one_mem, ExtFPf.oneF X, ExtFPf.oneF_mem X, ?_⟩, ?_, ?_⟩
    · rw [FundSetPf.lact_one, ExtFPf.rmul_oneF]
    · rintro x y ⟨γ, hγ, b, hb, rfl⟩
      refine ⟨γ⁻¹, X.Γ.inv_mem hγ, ExtFPf.invF X b, ExtFPf.invF_mem X hb, ?_⟩
      rw [← FundSetPf.lact_rmul, FundSetPf.lact_inv, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb,
        ExtFPf.rmul_oneF]
    · rintro x y z ⟨γ, hγ, b, hb, rfl⟩ ⟨γ', hγ', b', hb', rfl⟩
      refine ⟨γ' * γ, X.Γ.mul_mem hγ' hγ, rmul b b', ExtFPf.mul_mem X hb hb', ?_⟩
      rw [FundSetPf.lact_mul, ← FundSetPf.lact_rmul, ExtFPf.rmul_assoc]

theorem finite_orbits : ∀ (r : ℕ) (X : Data E r) (L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ),
    X.IsSec L w0 → (∀ k, X.IsSec L (s k)) →
    (∀ x ∈ X.dom, (∀ k, s k x = 0) → w0 x ≠ 0 ∧ (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      s k (cpt X x z) / w0 (cpt X x z) : V (nd X))) 0).det ≠ 0) →
    ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom →
    (∀ x ∈ X.dom, (∀ k, s k x = 0) → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C) →
    ∃ (δ : ℕ) (xs : Fin δ → Frame X.Ψ r), (∀ j, xs j ∈ X.dom) ∧
      (∀ x ∈ X.dom, (∀ k, s k x = 0) ↔ ∃ j, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (xs j) b)) ∧
      ∀ j j', ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, xs j' = lact γ (rmul (xs j) b) → j = j' := by
  classical
  intro r X L w0 s _ hs hsimp C hC hCd hmeet
  set S := orbitSetoid X with hS

  have hstab : ∀ x y, S.r x y → (x ∈ X.dom ∧ ∀ k, s k x = 0) → (y ∈ X.dom ∧ ∀ k, s k y = 0) := by
    rintro x y ⟨γ, hγ, b, hb, rfl⟩ ⟨hx, h0⟩
    have hxb := OntoS.dom_rmul X hx hb
    refine ⟨OntoS.dom_lact X hγ hxb, fun k => ?_⟩
    rw [(hs k).2.2 γ hγ _ hxb, (hs k).2.1 x hx b hb, h0 k, mul_zero, mul_zero]

  have hloc : ∀ x ∈ X.dom, (∀ k, s k x = 0) → ∀ᶠ y in 𝓝 x, (∀ k, s k y = 0) → S.r x y := by
    intro x hx h0
    obtain ⟨δ, hδ, hiso⟩ := isolated_of_det (hsimp x hx h0).2 (by
      ext k
      simp [cpt_origin, h0 k])
    filter_upwards [eventually_split X hx hδ] with y ⟨hy, z, hz, b, hb, he⟩ hy0
    have hR : S.r (cpt X x z) y := ⟨1, X.Γ.one_mem, b, hb, by rw [FundSetPf.lact_one]; exact he⟩
    have h1 := (hstab _ _ (S.iseqv.symm hR) ⟨hy, hy0⟩).2
    have hz0 : z = 0 := hiso z hz (by
      ext k
      simp [h1 k])
    rwa [hz0, cpt_origin] at hR
  have hK : IsCompact (C ∩ {x | ∀ k, s k x = 0}) := by
    have hcont : ContinuousOn (fun x k => s k x) C :=
      continuousOn_pi.2 fun k => (hs k).1.continuousOn.mono hCd
    have hcl := hcont.preimage_isClosed_of_isClosed hC.isClosed (isClosed_singleton (x := 0))
    have he : C ∩ {x | ∀ k, s k x = 0} = C ∩ (fun x k => s k x) ⁻¹' {0} := by
      ext x; simp [funext_iff]
    rw [he]
    exact hC.of_isClosed_subset hcl Set.inter_subset_left
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => {y | (∀ k, s k y = 0) → S.r x y})
    (fun x hx => hloc x (hCd hx.1) hx.2)
  set T : Finset (Quotient S) := t.image (Quotient.mk S) with hT
  have hout : ∀ q ∈ T, q.out ∈ X.dom ∧ ∀ k, s k q.out = 0 := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hq
    exact hstab x _ (S.iseqv.symm (Quotient.mk_out x)) ⟨hCd (htK x hx).1, (htK x hx).2⟩
  refine ⟨T.card, fun j => (T.equivFin.symm j).1.out, fun j => (hout _ (T.equivFin.symm j).2).1,
    fun x hx => ⟨fun h0 => ?_, ?_⟩, ?_⟩
  · obtain ⟨γ, hγ, b, hb, hc⟩ := hmeet x hx h0
    have hR : S.r x (lact γ (rmul x b)) := ⟨γ, hγ, b, hb, rfl⟩
    have h1 := (hstab _ _ hR ⟨hx, h0⟩).2
    obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hcov ⟨hc, h1⟩)
    refine ⟨T.equivFin ⟨Quotient.mk S u, Finset.mem_image_of_mem _ hu⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact S.iseqv.trans (Quotient.mk_out u) (S.iseqv.trans (hy h1) (S.iseqv.symm hR))
  · rintro ⟨j, hj⟩
    exact (hstab _ x hj (hout _ (T.equivFin.symm j).2)).2
  · intro j j' γ hγ b hb h
    have hR : S.r (T.equivFin.symm j).1.out (T.equivFin.symm j').1.out := ⟨γ, hγ, b, hb, h⟩
    have := Quotient.sound (s := S) hR
    rw [Quotient.out_eq, Quotient.out_eq] at this
    exact T.equivFin.symm.injective (Subtype.ext this)

end GlobalTheory.FiniteZeroOrbits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverUnitaryLatticeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.exists_finite_measure_cover_unitary_lattice : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ, (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
  first | exact @GlobalTheory.FiniteCovolume.exists_finite_measure_cover | exact GlobalTheory.FiniteCovolume.exists_finite_measure_cover | (intros; apply GlobalTheory.FiniteCovolume.exists_finite_measure_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IntegrandAemeasurable
section
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ContDiff ENNReal

namespace GlobalTheory.SkodaIter

noncomputable section

variable {n : ℕ} {U : Set (V n)}

def integrand (s : Fin n → V n → ℂ) (ph : V n → ℝ) (t : ℝ) (G : V n → ℂ) (z : V n) : ℝ≥0∞ :=
  ENNReal.ofReal (‖G z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-t) * Real.exp (-ph z))

theorem holo_val {f : V n → ℂ} (hf : DifferentiableOn ℂ f U) :
    Holo n (Subtype.val : U → V n) (fun x => f x.1) := by
  intro e he
  exact (hf.mono (HE.target_sub he)).congr (HE.comp_symm_eqOn f he)

theorem normSq_continuousOn {s : Fin n → V n → ℂ} (hs : ∀ k, DifferentiableOn ℂ (s k) U) :
    ContinuousOn (fun z => ∑ k, ‖s k z‖ ^ 2) U := by
  exact continuousOn_finsetSum _ (fun k _ => ((hs k).continuousOn.norm).pow 2)

theorem normSq_pos {s : Fin n → V n → ℂ} {z : V n} {k : Fin n} (h : s k z ≠ 0) :
    0 < ∑ k, ‖s k z‖ ^ 2 := by
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr h) 2)
    (Finset.single_le_sum (f := fun j => ‖s j z‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ k))

theorem extend (hU : IsOpen U) {s : Fin n → V n → ℂ} (k0 : Fin n)
    (hs : ∀ k, DifferentiableOn ℂ (s k) U)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, s k0 y ≠ 0)
    {ph : V n → ℝ} (hph : ContinuousOn ph U) {t : ℝ} (ht : 0 ≤ t) {G : V n → ℂ}
    (hG : DifferentiableOn ℂ G {y | y ∈ U ∧ s k0 y ≠ 0})
    (hI : ∫⁻ z in {y | y ∈ U ∧ s k0 y ≠ 0}, integrand s ph t G z < ⊤) :
    ∃ G' : V n → ℂ, DifferentiableOn ℂ G' U ∧ Set.EqOn G' G {y | y ∈ U ∧ s k0 y ≠ 0} ∧
      ∫⁻ z in U, integrand s ph t G' z < ⊤ := by
  have hM : IsOpen {y | y ∈ U ∧ s k0 y ≠ 0} := HE.isOpen_punct hU (hs k0)
  have hloc : ∀ p ∈ U, ∃ ρ > 0, ball p ρ ⊆ U ∧
      ∫⁻ y in ball p ρ \ {y | s k0 y = 0}, ENNReal.ofReal (‖G y‖ ^ 2) < ⊤ := by
    intro p hp
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU p hp
    have hKU : closedBall p (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
    have hbU : ball p (ε / 2) ⊆ U := ball_subset_closedBall.trans hKU
    have hK : IsCompact (closedBall p (ε / 2)) := isCompact_closedBall p _
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn ((normSq_continuousOn hs).mono hKU)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hph.mono hKU)
    refine ⟨ε / 2, half_pos hε, hbU, ?_⟩
    have hAM : ball p (ε / 2) \ {y | s k0 y = 0} ⊆ {y | y ∈ U ∧ s k0 y ≠ 0} :=
      fun y hy => ⟨hbU hy.1, hy.2⟩
    have hAeq : ball p (ε / 2) \ {y | s k0 y = 0} = ball p (ε / 2) ∩ {y | y ∈ U ∧ s k0 y ≠ 0} := by
      ext y
      exact ⟨fun h => ⟨h.1, hbU h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    have hAm : MeasurableSet (ball p (ε / 2) \ {y | s k0 y = 0}) := by
      rw [hAeq]; exact (isOpen_ball.inter hM).measurableSet
    have hpt : ∀ y ∈ ball p (ε / 2) \ {y | s k0 y = 0},
        ENNReal.ofReal (‖G y‖ ^ 2) ≤ ENNReal.ofReal (B ^ t * Real.exp C) * integrand s ph t G y := by
      intro y hy
      have hyK : y ∈ closedBall p (ε / 2) := ball_subset_closedBall hy.1
      have hpos : 0 < ∑ k, ‖s k y‖ ^ 2 := normSq_pos (k := k0) hy.2
      have hfB : ∑ k, ‖s k y‖ ^ 2 ≤ B := (Real.le_norm_self _).trans (hB y hyK)
      have hB0 : 0 < B := hpos.trans_le hfB
      have hphC : ph y ≤ C := (Real.le_norm_self _).trans (hC y hyK)
      have h1 : 1 ≤ (∑ k, ‖s k y‖ ^ 2) ^ (-t) * B ^ t := by
        rw [Real.rpow_neg hpos.le, inv_mul_eq_div, one_le_div (Real.rpow_pos_of_pos hpos t)]
        exact Real.rpow_le_rpow hpos.le hfB ht
      have h2 : 1 ≤ Real.exp C * Real.exp (-ph y) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
      have h3 := mul_le_mul h1 h2 zero_le_one (le_trans zero_le_one h1)
      simp only [integrand]
      rw [← ENNReal.ofReal_mul (mul_pos (Real.rpow_pos_of_pos hB0 t) (Real.exp_pos C)).le]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg ‖G y‖)]
    calc ∫⁻ y in ball p (ε / 2) \ {y | s k0 y = 0}, ENNReal.ofReal (‖G y‖ ^ 2)
        ≤ ∫⁻ y in ball p (ε / 2) \ {y | s k0 y = 0},
            ENNReal.ofReal (B ^ t * Real.exp C) * integrand s ph t G y :=
          lintegral_mono_ae (ae_restrict_of_forall_mem hAm hpt)
      _ = ENNReal.ofReal (B ^ t * Real.exp C) *
            ∫⁻ y in ball p (ε / 2) \ {y | s k0 y = 0}, integrand s ph t G y :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (B ^ t * Real.exp C) *
            ∫⁻ y in {y | y ∈ U ∧ s k0 y ≠ 0}, integrand s ph t G y :=
          mul_le_mul (le_refl _) (lintegral_mono_set hAM) zero_le zero_le
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI
  obtain ⟨G', hG'd, hG'eq⟩ := HE.ext_glue hU (s k0) G (hs k0) hgn hG hloc
  refine ⟨G', hG'd, hG'eq, ?_⟩
  have hnull : volume {y | y ∈ U ∧ s k0 y = 0} = 0 := HE.zeros_null hU (hs k0) hgn
  have hae : (U : Set (V n)) =ᵐ[volume] {y | y ∈ U ∧ s k0 y ≠ 0} := by
    have e1 : volume (U \ {y | y ∈ U ∧ s k0 y ≠ 0}) = 0 :=
      measure_mono_null (fun y (hy : y ∈ U \ {y | y ∈ U ∧ s k0 y ≠ 0}) =>
        (⟨hy.1, Classical.byContradiction fun h => hy.2 ⟨hy.1, h⟩⟩ : y ∈ {y | y ∈ U ∧ s k0 y = 0})) hnull
    have e2 : volume ({y | y ∈ U ∧ s k0 y ≠ 0} \ U) = 0 :=
      measure_mono_null (fun y hy => (hy.2 hy.1.1).elim) measure_empty
    exact (ae_eq_set (μ := volume)).2 ⟨e1, e2⟩
  rw [Measure.restrict_congr_set hae]
  rw [lintegral_congr_ae (ae_restrict_of_forall_mem hM.measurableSet
    (fun y hy => show integrand s ph t G' y = integrand s ph t G y by simp only [integrand, hG'eq hy]))]
  exact hI

theorem step (hn : 2 ≤ n) (hU : IsOpen U) {s : Fin n → V n → ℂ} (k0 : Fin n)
    (hs : ∀ k, DifferentiableOn ℂ (s k) U)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, s k0 y ≠ 0)
    (hS : ∃ S : EtaleStein n {z | z ∈ U ∧ s k0 z ≠ 0}, S.z = Subtype.val)
    {ph : V n → ℝ} (hph : ContDiffOn ℝ ∞ ph U)
    (hl : ∀ z ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => ((ph w : ℝ) : ℂ)) z ξ).re)
    {t : ℝ} (ht : (n : ℝ) - 1 < t) {F : V n → ℂ} (hF : DifferentiableOn ℂ F U)
    (hI : ∫⁻ z in U, integrand s ph (t + 1) F z < ⊤) :
    ∃ h : Fin n → V n → ℂ, (∀ i, DifferentiableOn ℂ (h i) U ∧
      ∫⁻ z in U, integrand s ph t (h i) z < ⊤) ∧ ∀ z ∈ U, F z = ∑ i, s i z * h i z := by
  obtain ⟨S, hSz⟩ := hS
  have hM : IsOpen {z | z ∈ U ∧ s k0 z ≠ 0} := HE.isOpen_punct hU (hs k0)
  have ht0 : 0 ≤ t := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hint : ∫⁻ x, ENNReal.ofReal (‖F x.1‖ ^ 2 * (∑ i, ‖s i x.1‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph x.1))
      ∂(vol n S.z) < ⊤ := by
    rw [hSz]
    refine (HE.lintegral_val hM (fun y => ENNReal.ofReal (‖F y‖ ^ 2 * (∑ i, ‖s i y‖ ^ 2) ^ (-(t + 1)) *
      Real.exp (-ph y)))).trans_lt ?_
    exact lt_of_le_of_lt (lintegral_mono_set (fun y hy => hy.1)) hI
  obtain ⟨hh, hhh, hdec, hbound⟩ := ReciprocityTheory.L2DbarEstimates.skoda n _ S n (fun i x => s i x.1) (fun x => ph x.1) t
    (fun x => F x.1) hn
    (fun i => by rw [hSz]; exact holo_val ((hs i).mono (fun y hy => hy.1)))
    (fun x => ⟨k0, x.2.2⟩)
    (by rw [hSz]; exact HE.smoothR_val (hph.mono (fun y hy => hy.1)))
    (by rw [hSz]; intro x ξ; rw [HE.levi_val hM ph x ξ]; exact hl x.1 x.2.1 ξ)
    ht
    (by rw [hSz]; exact holo_val (hF.mono (fun y hy => hy.1)))
    hint
  have hfin := lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint)
  rw [hSz] at hfin
  have hhv : ∀ i, Holo n (Subtype.val : {z // z ∈ {z | z ∈ U ∧ s k0 z ≠ 0}} → V n) (hh i) := by
    intro i; rw [← hSz]; exact hhh i
  have hGd : ∀ i, DifferentiableOn ℂ (HE.ext0 (hh i)) {z | z ∈ U ∧ s k0 z ≠ 0} :=
    fun i => HE.differentiableOn_extendByZero hM (hhv i)
  have hGi : ∀ i, ∫⁻ y in {z | z ∈ U ∧ s k0 z ≠ 0}, integrand s ph t (HE.ext0 (hh i)) y < ⊤ := by
    intro i
    refine ((HE.lintegral_val hM (fun y => integrand s ph t (HE.ext0 (hh i)) y)).symm.trans_le ?_).trans_lt hfin
    refine lintegral_mono (fun x => ?_)
    simp only [integrand, HE.extendByZeroOnSubset_apply_coe]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun j => ‖hh j x‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))
      (Real.rpow_nonneg (by positivity) _)) (Real.exp_pos _).le
  choose H hHd hHeq hHint using fun i => extend hU k0 hs hgn hph.continuousOn ht0 (hGd i) (hGi i)
  refine ⟨H, fun i => ⟨hHd i, hHint i⟩, ?_⟩
  have hDc : ContinuousOn (fun z => F z - ∑ i, s i z * H i z) U :=
    hF.continuousOn.sub (continuousOn_finsetSum _ (fun i _ => (hs i).continuousOn.mul (hHd i).continuousOn))
  intro z hz
  by_contra hne
  have hW := hDc.isOpen_inter_preimage hU (isOpen_compl_singleton (x := (0:ℂ)))
  obtain ⟨y, ⟨hyU, hyD⟩, hy0⟩ := hgn _ hW Set.inter_subset_left ⟨z, hz, by simpa [sub_eq_zero] using hne⟩
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hyD
  apply hyD
  have hd := hdec ⟨y, hyU, hy0⟩
  dsimp only at hd
  rw [sub_eq_zero, hd]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hHeq i ⟨hyU, hy0⟩]
  exact (congrArg (fun w => s i y * w) (HE.extendByZeroOnSubset_apply_coe (hh i) ⟨y, hyU, hy0⟩)).symm

end

end GlobalTheory.SkodaIter
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KaUnfoldOfUnfoldOfKappa
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kaUnfold_of_unfold_of_kappa :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ ψ : Frame X.Ψ r → ℝ≥0∞, Measurable ψ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 = ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ bb : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∃ κ : Frame X.Ψ r → ℝ, Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → (KaUnfoldStatement (E := E)) := by
  intro hU hK r X x0 ho hP FF hFF bb hbb
  obtain ⟨κ, hκm, hκ1, hκB, hκka, ⟨C, hC, hsum⟩, -⟩ := hK r X x0 ho hP bb hbb
  refine ⟨C, hC, fun φ hφm hφB hφΓ => ?_⟩
  have h1 : ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * φ (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z, ENNReal.ofReal (κ (cpt X x0 z)) * φ (cpt X x0 z) ∂muF X x0 :=
    lintegral_congr_ae ((OntoH.ae_mem_Om X x0).mono fun z hz => by simp only [hκka z hz])
  have h2 := hU r X x0 ho FF hFF (fun x => ENNReal.ofReal (κ x) * φ x)
    (hκm.ennreal_ofReal.mul hφm) (fun x hx b hb => by simp only [hκB x hx b hb, hφB x hx b hb])
  rw [h1, h2, ← lintegral_const_mul' _ _ hC.ne]
  refine setLIntegral_mono' hFF.1 fun z hz => ?_
  have hx : cpt X x0 z ∈ X.dom := hFF.2.1 hz
  calc ∑' γ : X.Γ, ENNReal.ofReal (κ (lact γ.1 (cpt X x0 z))) * φ (lact γ.1 (cpt X x0 z))
      ≤ ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 (cpt X x0 z)))) * φ (cpt X x0 z) := by
        refine ENNReal.tsum_le_tsum fun γ => ?_
        rw [hφΓ γ.1 γ.2 _ hx]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        obtain ⟨h0, h1⟩ := hκ1 _ (OntoS.dom_lact X γ.2 hx)
        rw [Real.le_sqrt h0.le h0.le]
        nlinarith
    _ = (∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 (cpt X x0 z))))) * φ (cpt X x0 z) :=
        ENNReal.tsum_mul_right
    _ ≤ C * φ (cpt X x0 z) := mul_le_mul' (hsum _ hx) le_rfl

end GlobalTheory
end

