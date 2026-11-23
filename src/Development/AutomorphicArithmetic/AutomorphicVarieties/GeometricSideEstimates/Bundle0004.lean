module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.PositivityAtAllPlaces
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.Reduction

private theorem cont_pInf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] : Continuous (pInf E) := by
  have c2 : Continuous (infEq E).symm := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact c2.comp continuous_fst

private theorem pInf_pos {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (s : ℝ) (hs : 0 < s) :
    pInf E ((posIdele (K := E) s hs : GroundTheory.Global.IdeleGroup E) : Ad E) = fun _ => (s : ℂ) := by
  funext w
  have hw : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
  have h : ((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).1 w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (s : ℂ) := by
    rw [← GroundTheory.Global.IdeleGroup.coe_infiniteProj, infiniteProj_posIdele]
    change GroundTheory.Global.posRealElem w _ = _
    unfold GroundTheory.Global.posRealElem
    rw [dite_eq_right hw]
    simp [InfinitePlace.mult, hw, Real.sqrt_sq hs.le]
  change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))
    (((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).1 w) = _
  rw [h, RingEquiv.apply_symm_apply]

private theorem pFin_pos {E : Type} [Field E] [NumberField E] (s : ℝ) (hs : 0 < s) :
    pFin E ((posIdele (K := E) s hs : GroundTheory.Global.IdeleGroup E) : Ad E) = 1 := by
  change ((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).2 = (1 : Af E)
  exact IsDedekindDomain.FiniteAdeleRing.ext _ fun v => by rw [posIdele_finite]; rfl

private theorem col_eq {R : Type} [CommRing R] {a : ℕ} (i₀ : Fin a) (g γ b d k : GL (Fin a) R) (u : Fin a → R)
    (hd : d.val = Matrix.diagonal u) (hb : ∀ i, i ≠ i₀ → (b⁻¹).val i i₀ = 0) (h : γ * g = b * d * k) :
    u i₀ • ((g⁻¹).val *ᵥ fun i => (γ⁻¹).val i i₀) = fun i => (k⁻¹ * b⁻¹).val i i₀ := by
  have h1 : g⁻¹ * γ⁻¹ = k⁻¹ * d⁻¹ * b⁻¹ := by
    rw [← _root_.mul_inv_rev, h]; simp [mul_assoc]
  have h2 : ((g⁻¹).val *ᵥ fun i => (γ⁻¹).val i i₀) = (k⁻¹ * d⁻¹).val *ᵥ fun i => (b⁻¹).val i i₀ := by
    funext i
    have := congrArg (fun x : GL (Fin a) R => x.val i i₀) h1
    simpa only [Units.val_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have h3 : u i₀ • (fun i => (b⁻¹).val i i₀) = d.val *ᵥ fun i => (b⁻¹).val i i₀ := by
    funext i
    rw [hd, Matrix.mulVec_diagonal]
    by_cases hi : i = i₀
    · subst hi; rfl
    · simp only [Pi.smul_apply, hb i hi, smul_zero, mul_zero]
  rw [h2, ← Matrix.mulVec_smul, h3, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right]
  rfl

theorem UpperTheory.positivity_at_all_places :
    SiegelCol := by
  intro E _ _ _ a ha
  obtain ⟨Ω, C, N, hΩ, hB, hS⟩ := UpperTheory.height_bound_of_quasiHeight_le E a
  obtain ⟨-, -, -, hsm, -, -⟩ := UpperTheory.geometric_side_quadraticForm_identity E a
  let i₀ : Fin a := ⟨0, ha⟩
  have hK : IsCompact (maxCompact (K := E) (n := a) : Set (GA E a)) := isCompact_maxCompact
  let f : GA E a × GA E a → Fin a → Ad E := fun p i => (p.1⁻¹ * p.2⁻¹).val i i₀
  have hf : Continuous f := continuous_pi fun i =>
    (Units.continuous_val.comp (continuous_fst.inv.mul continuous_snd.inv)).matrix_elem i i₀
  have hc := hK.prod hΩ
  have hF : Continuous fun p i => pFin E (f p i) := continuous_pi fun i =>
    continuous_snd.comp ((continuous_apply i).comp hf)
  have hI : Continuous fun p => qf (fun i => pInf E (f p i)) := by
    unfold qf
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun w _ =>
      (((continuous_apply w).comp (cont_pInf.comp ((continuous_apply i).comp hf))).norm).pow 2
  obtain ⟨M, hM⟩ := hc.bddAbove_image hI.continuousOn
  refine ⟨_, |C| * M ^ N, N, hc.image hF, fun g => ?_⟩
  obtain ⟨γ, b, k, ρ, hρ, hb, hk, he, hh⟩ := hS g
  have hh0 := (hh i₀).2 rfl
  have hcol := col_eq i₀ (g.1 : GA E a) (ratGL E a γ) b _ k
    (fun i => ((posIdele (K := E) (ρ i) (hρ i) : GroundTheory.Global.IdeleGroup E) : Ad E)) (coe_diagUnits _ _)
    (fun i hi => mem_adelicBorel.1 (inv_mem (hB b hb)) (Fin.lt_def.2 (Nat.pos_of_ne_zero fun h => hi (Fin.ext h)))) he
  have hγ : (fun i => ((ratGL E a γ)⁻¹).val i i₀) = fun i => algebraMap E (Ad E) ((γ⁻¹).val i i₀) := by
    rw [← map_inv]; rfl
  rw [hγ] at hcol
  refine ⟨fun i => (γ⁻¹).val i i₀, fun h0 => ?_, ⟨(k, b), ⟨hk, hb⟩, ?_⟩, ?_⟩
  · have h1 : (γ * γ⁻¹).val i₀ i₀ = 0 := by
      rw [Units.val_mul, Matrix.mul_apply]
      exact Finset.sum_eq_zero fun j _ => by rw [congrFun h0 j]; simp
    simp at h1
  · funext i
    have h1 := congrArg (pFin E) (congrFun hcol i)
    rw [Pi.smul_apply, smul_eq_mul, map_mul, pFin_pos, one_mul, RingHom.map_mulVec] at h1
    exact h1.symm
  · have h1 : (fun i => pInf E (f (k, b) i)) =
        ρ i₀ • ((GeneralLinearGroup.map (pInf E) (g.1⁻¹ : GA E a)).val *ᵥ vInf fun i => (γ⁻¹).val i i₀) := by
      funext i
      have h1 := congrArg (pInf E) (congrFun hcol i)
      rw [Pi.smul_apply, smul_eq_mul, map_mul, pInf_pos, RingHom.map_mulVec] at h1
      refine h1.symm.trans ?_
      funext w
      rw [Pi.smul_apply, Pi.smul_apply, Complex.real_smul]
      rfl
    have h2 : qf (fun i => pInf E (f (k, b) i)) ≤ M := hM ⟨(k, b), ⟨hk, hb⟩, rfl⟩
    rw [h1, hsm] at h2
    set q := qf ((GeneralLinearGroup.map (pInf E) (g.1⁻¹ : GA E a)).val *ᵥ vInf fun i => (γ⁻¹).val i i₀) with hq
    have hq0 : 0 ≤ q := qf_nonneg _
    calc _ ≤ C * ρ i₀ ^ (2 * N) * q ^ N := mul_le_mul_of_nonneg_right hh0 (pow_nonneg hq0 N)
      _ = C * (ρ i₀ ^ 2 * q) ^ N := by rw [mul_pow, ← pow_mul, mul_assoc]
      _ ≤ |C| * M ^ N := mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity) h2 N) (by positivity) (abs_nonneg C)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.ScalingInvarianceOfGeometricFunctional
section
open UpperTheory.V.Lit.Geo

private theorem scale_mono {ι : Type} {q : ι → ℝ} {N M : ℕ} (h : Scale q N) (hNM : N ≤ M) : Scale q M := by
  refine ⟨h.1, fun s t hs hst => ⟨(h.2 s t hs hst).1, (h.2 s t hs hst).2.trans ?_⟩⟩
  refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ((one_le_div hs).2 hst) hNM) ?_
  exact tsum_nonneg fun i => (Real.exp_pos _).le

private theorem scale_equiv {ι κ : Type} (e : ι ≃ κ) {q : κ → ℝ} {N : ℕ} (h : Scale q N) :
    Scale (fun i => q (e i)) N := by
  refine ⟨fun i => h.1 _, fun s t hs hst => ⟨?_, ?_⟩⟩
  · exact (e.summable_iff (f := fun k => Real.exp (-Real.pi * (s * q k)))).2 (h.2 s t hs hst).1
  · rw [e.tsum_eq (fun k => Real.exp (-Real.pi * (s * q k))), e.tsum_eq (fun k => Real.exp (-Real.pi * (t * q k)))]
    exact (h.2 s t hs hst).2

theorem UpperTheory.scaling_invariance_of_geometric_functional :
    ScaleGen := by
  intro A V _ _ _ _ φ ε hε hφ
  let W : Submodule ℝ V := Submodule.span ℝ (Set.range φ)
  let L : Submodule ℤ W := (φ.range.comap W.subtype.toAddMonoidHom).toIntSubmodule
  have hmem : ∀ w : W, w ∈ L ↔ (w : V) ∈ Set.range φ := fun w => Iff.rfl
  have hnorm : ∀ y : L, y ≠ 0 → ε ≤ ‖y‖ := by
    intro y hy
    obtain ⟨a, ha⟩ := (hmem y).1 y.2
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply hy
      apply Subtype.ext
      apply Subtype.ext
      simpa using ha.symm
    have := hφ a ha0
    rw [ha] at this
    exact this
  haveI : DiscreteTopology L := by
    apply discreteTopology_of_isOpen_singleton_zero
    rw [Metric.isOpen_singleton_iff]
    refine ⟨ε, hε, fun y hy => ?_⟩
    by_contra hne
    rw [dist_zero_right] at hy
    linarith [hnorm y hne]
  haveI : IsZLattice ℝ L := by
    refine ⟨?_⟩
    have hs : (L : Set W) = ((↑) : W → V) ⁻¹' Set.range φ := rfl
    rw [hs]
    exact Submodule.span_span_coe_preimage
  have hinj : Function.Injective φ := by
    intro a b hab
    by_contra hne
    have h0 := hφ (a - b) (sub_ne_zero.mpr hne)
    rw [map_sub, hab, sub_self, norm_zero] at h0
    linarith
  let e : A ≃ L := Equiv.ofBijective
    (fun a => ⟨⟨φ a, Submodule.subset_span ⟨a, rfl⟩⟩, ⟨a, rfl⟩⟩)
    ⟨fun a b hab => hinj (congrArg (fun y : L => ((y : W) : V)) hab), fun y => by
      obtain ⟨a, ha⟩ := (hmem y).1 y.2
      exact ⟨a, Subtype.ext (Subtype.ext ha)⟩⟩
  have hL := UpperTheory.geometric_side_estimate W L
  have h1 := scale_equiv e hL
  exact scale_mono h1 (Submodule.finrank_le W)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.SecondOrderTaylorRemainderBound
section
open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Lit.Bor

private theorem taylor_two {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : V → ℝ} {x : V}
    (hf : ContDiffAt ℝ 2 f x) : ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ∀ y : V, ‖y‖ ≤ ε →
      |f (x + y) - f x - fderiv ℝ f x y| ≤ C * ‖y‖ ^ 2 := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h1.exists_lipschitzOnWith
  have h2 : ∀ᶠ z in nhds x, DifferentiableAt ℝ f z :=
    (hf.eventually (by simp)).mono fun z hz => hz.differentiableAt (by simp)
  obtain ⟨ε, hε, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem ht h2)
  refine ⟨K, ε, K.2, hε, fun y hy => ?_⟩
  have hsub : Metric.closedBall x ‖y‖ ⊆ Metric.closedBall x ε := Metric.closedBall_subset_closedBall hy
  have hx : x ∈ Metric.closedBall x ‖y‖ := Metric.mem_closedBall_self (norm_nonneg _)
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (𝕜 := ℝ) (f := f) (f' := fderiv ℝ f)
    (φ := fderiv ℝ f x) (C := K * ‖y‖) (s := Metric.closedBall x ‖y‖) (x := x) (y := x + y)
    (fun z hz => (hb (hsub hz)).2.hasFDerivAt.hasFDerivWithinAt)
    (fun z hz => by
      have := hK.norm_sub_le (hb (hsub hz)).1 (hb (hsub hx)).1
      refine this.trans (mul_le_mul_of_nonneg_left ?_ K.2)
      rwa [← dist_eq_norm])
    (convex_closedBall _ _) hx (by simp)
  rw [add_sub_cancel_left, Real.norm_eq_abs] at key
  calc _ ≤ _ := key
    _ = _ := by ring

theorem UpperTheory.second_order_taylor_remainder_bound :
    ScTaylor := by
  intro E _ _ a
  obtain ⟨hs, h1, hd, -⟩ := UpperTheory.deriv_similitudeChar_at_one_eq_trace E a
  have hat : ContDiffAt ℝ 2 (fun y : Lie E a => sc (Matrix.of y)) (oneL E a) :=
    (hs.contDiffAt (isOpen_invSet.mem_nhds (val_mem_invSet 1))).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  obtain ⟨C, ε, hC, hε, h⟩ := taylor_two hat
  refine ⟨C, ε, hC, hε, fun Y hY => ?_⟩
  have := h (toL Y) hY
  rw [hd, sub_neg_eq_add] at this
  have e : sc (Matrix.of (oneL E a)) = 1 := h1
  rw [e] at this
  exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.TwoSidedBoundOfPointwiseBounds
section
open UpperTheory.V.Lit.Geo

private theorem exp_quad (x : ℝ) : Real.exp x ≤ 1 + x + x ^ 2 * Real.exp |x| := by
  rcases le_or_gt |x| 1 with h | h
  · have h1 := Real.abs_exp_sub_one_sub_id_le h
    have h2 : x ^ 2 ≤ x ^ 2 * Real.exp |x| :=
      le_mul_of_one_le_right (sq_nonneg x) (Real.one_le_exp (abs_nonneg x))
    have h3 := (abs_le.mp h1).2
    linarith
  · rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx] at h ⊢
      have : Real.exp x ≤ x ^ 2 * Real.exp x :=
        le_mul_of_one_le_left (Real.exp_pos x).le (by nlinarith)
      linarith
    · rw [abs_of_neg hx] at h ⊢
      have h1 : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx.le
      have h2 : x ^ 2 ≤ x ^ 2 * Real.exp (-x) :=
        le_mul_of_one_le_right (sq_nonneg x) (Real.one_le_exp (by linarith))
      nlinarith

private theorem up_pt (q u ε : ℝ) (hq : 0 ≤ q) (h0 : 0 ≤ ε) (h4 : ε ≤ 1 / 4) (hu : |u| ≤ ε * q) :
    Real.exp (-Real.pi * (q + u)) ≤ Real.exp (-Real.pi * q) + -Real.pi * (u * Real.exp (-Real.pi * q)) +
      32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) := by
  have hpi := Real.pi_pos
  have hE : Real.exp (-Real.pi * (q + u)) = Real.exp (-Real.pi * q) * Real.exp (-Real.pi * u) := by
    rw [← Real.exp_add]; congr 1; ring
  have hx := exp_quad (-Real.pi * u)
  have habs : |-Real.pi * u| = Real.pi * |u| := by
    rw [abs_mul, abs_neg, abs_of_pos hpi]
  rw [habs] at hx
  have hu4 : |u| ≤ q / 4 := by nlinarith [abs_nonneg u, mul_nonneg (sub_nonneg.mpr h4) hq]
  have hu2 : u ^ 2 ≤ ε ^ 2 * q ^ 2 := by
    have := mul_self_le_mul_self (abs_nonneg u) hu
    nlinarith [sq_abs u]
  have hpu : Real.pi * |u| ≤ Real.pi * (q / 4) := mul_le_mul_of_nonneg_left hu4 hpi.le
  have hy0 : 0 ≤ Real.pi * q / 4 := by positivity
  have hexp1 : Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q) ≤
      Real.exp (-Real.pi * (1 / 2 * q)) * Real.exp (-(Real.pi * q / 4)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hquad : (Real.pi * q / 4) ^ 2 ≤ 2 * Real.exp (Real.pi * q / 4) := by
    have := Real.quadratic_le_exp_of_nonneg hy0
    nlinarith
  have hey : (Real.pi * q / 4) ^ 2 * Real.exp (-(Real.pi * q / 4)) ≤ 2 := by
    have h1 : Real.exp (Real.pi * q / 4) * Real.exp (-(Real.pi * q / 4)) = 1 := by
      rw [← Real.exp_add]; simp
    have h2 := Real.exp_pos (-(Real.pi * q / 4))
    nlinarith
  have A : (-Real.pi * u) ^ 2 ≤ ε ^ 2 * (Real.pi ^ 2 * q ^ 2) := by
    have : (-Real.pi * u) ^ 2 = Real.pi ^ 2 * u ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg Real.pi]
  have hterm : (-Real.pi * u) ^ 2 * Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q) ≤
      32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) := by
    calc (-Real.pi * u) ^ 2 * Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q)
        = (-Real.pi * u) ^ 2 * (Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q)) := by ring
      _ ≤ (ε ^ 2 * (Real.pi ^ 2 * q ^ 2)) *
            (Real.exp (-Real.pi * (1 / 2 * q)) * Real.exp (-(Real.pi * q / 4))) :=
          mul_le_mul A hexp1 (by positivity) (by positivity)
      _ = 16 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) *
            ((Real.pi * q / 4) ^ 2 * Real.exp (-(Real.pi * q / 4))) := by ring
      _ ≤ 16 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) * 2 := by gcongr
      _ = 32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) := by ring
  rw [hE]
  have hE0 := Real.exp_pos (-Real.pi * q)
  have hm := mul_le_mul_of_nonneg_left hx hE0.le
  nlinarith

private theorem low_pt (q u m : ℝ) :
    Real.exp m * ((1 - m) * Real.exp (-Real.pi * q) + -Real.pi * (u * Real.exp (-Real.pi * q))) ≤
      Real.exp (-Real.pi * (q + u)) := by
  have h := Real.add_one_le_exp (-Real.pi * u - m)
  have hE : Real.exp (-Real.pi * (q + u)) =
      Real.exp m * Real.exp (-Real.pi * q) * Real.exp (-Real.pi * u - m) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [hE]
  have hp : 0 ≤ Real.exp m * Real.exp (-Real.pi * q) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h hp]

private theorem sum_pt (q u ε : ℝ) (hq : 0 ≤ q) (h4 : ε ≤ 1 / 4) (hu : |u| ≤ ε * q) :
    ‖u * Real.exp (-Real.pi * q)‖ ≤ Real.exp (-Real.pi * (1 / 2 * q)) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hu4 : |u| ≤ q / 4 := by nlinarith [mul_nonneg (sub_nonneg.mpr h4) hq]
  have hpi := Real.pi_pos
  have h1 := Real.add_one_le_exp (Real.pi * q / 2)
  have hsplit : Real.exp (-Real.pi * (1 / 2 * q)) =
      Real.exp (-Real.pi * q) * Real.exp (Real.pi * q / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit]
  have hE := Real.exp_pos (-Real.pi * q)
  have h2 : q / 4 ≤ Real.exp (Real.pi * q / 2) := by nlinarith [Real.pi_gt_three]
  calc |u| * Real.exp (-Real.pi * q) ≤ q / 4 * Real.exp (-Real.pi * q) :=
        mul_le_mul_of_nonneg_right hu4 hE.le
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2 hE.le

theorem UpperTheory.two_sided_bound_of_pointwise_bounds :
    LogTaylor := by
  intro N
  refine ⟨32 * 2 ^ N, by positivity, ?_⟩
  intro ι _ q u ε hS h0 h4 hu
  obtain ⟨hq, hsc⟩ := hS
  have hsum1 := (hsc 1 1 one_pos le_rfl).1
  simp only [one_mul] at hsum1
  have hhalf := hsc (1 / 2) 1 (by norm_num) (by norm_num)
  have hsumh : Summable fun i => Real.exp (-Real.pi * (1 / 2 * q i)) := hhalf.1
  have hSle : ∑' i, Real.exp (-Real.pi * (1 / 2 * q i)) ≤
      2 ^ N * ∑' i, Real.exp (-Real.pi * q i) := by
    have h := hhalf.2
    have h2 : (1 : ℝ) / (1 / 2) = 2 := by norm_num
    rw [h2] at h
    simp only [one_mul] at h
    exact h
  set Z := ∑' i, Real.exp (-Real.pi * q i) with hZ
  set Z' := ∑' i, Real.exp (-Real.pi * (q i + u i)) with hZ'
  set M := ∑' i, u i * Real.exp (-Real.pi * q i) with hM
  set S := ∑' i, Real.exp (-Real.pi * (1 / 2 * q i)) with hS'
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hZpos : 0 < Z := hsum1.tsum_pos (fun i => (Real.exp_pos _).le) i0 (Real.exp_pos _)
  have hsumM : Summable fun i => u i * Real.exp (-Real.pi * q i) :=
    Summable.of_norm_bounded hsumh (fun i => sum_pt (q i) (u i) ε (hq i) h4 (hu i))
  have hR : HasSum (fun i => Real.exp (-Real.pi * q i) + -Real.pi * (u i * Real.exp (-Real.pi * q i)) +
      32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q i))) (Z + -Real.pi * M + 32 * ε ^ 2 * S) :=
    (hsum1.hasSum.add (hsumM.hasSum.mul_left _)).add (hsumh.hasSum.mul_left _)
  have hsum' : Summable fun i => Real.exp (-Real.pi * (q i + u i)) :=
    Summable.of_nonneg_of_le (fun i => (Real.exp_pos _).le)
      (fun i => up_pt (q i) (u i) ε (hq i) h0 h4 (hu i)) hR.summable
  have hup : Z' ≤ Z + -Real.pi * M + 32 * ε ^ 2 * S := by
    rw [← hR.tsum_eq]
    exact Summable.tsum_le_tsum (fun i => up_pt (q i) (u i) ε (hq i) h0 h4 (hu i)) hsum' hR.summable
  set m := -Real.pi * M / Z with hm
  have hmZ : m * Z = -Real.pi * M := by rw [hm]; exact div_mul_cancel₀ _ hZpos.ne'
  have hlow : Real.exp m * Z ≤ Z' := by
    have hL : HasSum (fun i => Real.exp m * ((1 - m) * Real.exp (-Real.pi * q i) +
        -Real.pi * (u i * Real.exp (-Real.pi * q i)))) (Real.exp m * ((1 - m) * Z + -Real.pi * M)) :=
      ((hsum1.hasSum.mul_left (1 - m)).add (hsumM.hasSum.mul_left (-Real.pi))).mul_left (Real.exp m)
    have e : (1 - m) * Z + -Real.pi * M = Z := by linear_combination (-1 : ℝ) * hmZ
    rw [← e, ← hL.tsum_eq]
    exact Summable.tsum_le_tsum (fun i => low_pt (q i) (u i) m) hL.summable hsum'
  have hZ'pos : 0 < Z' := lt_of_lt_of_le (by positivity) hlow
  have hLo : m ≤ Real.log Z' - Real.log Z := by
    have := Real.log_le_log (by positivity) hlow
    rw [Real.log_mul (Real.exp_pos m).ne' hZpos.ne', Real.log_exp] at this
    linarith
  have hUp : Real.log Z' - Real.log Z ≤ m + 32 * 2 ^ N * ε ^ 2 := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hZ'pos hZpos)
    rw [Real.log_div hZ'pos.ne' hZpos.ne'] at h1
    have h2 : Z' / Z - 1 ≤ m + 32 * 2 ^ N * ε ^ 2 := by
      rw [div_sub_one hZpos.ne', div_le_iff₀ hZpos]
      have h3 := mul_le_mul_of_nonneg_left hSle (by positivity : (0 : ℝ) ≤ 32 * ε ^ 2)
      nlinarith
    linarith
  have hexpr : Real.pi * (M / Z) = -m := by rw [hm]; ring
  rw [hexpr, abs_le]
  have hK : (0 : ℝ) ≤ 32 * 2 ^ N * ε ^ 2 := by positivity
  constructor <;> linarith
end

