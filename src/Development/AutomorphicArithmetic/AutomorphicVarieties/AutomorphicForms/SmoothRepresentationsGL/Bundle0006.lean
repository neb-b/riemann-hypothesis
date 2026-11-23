module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import GroundTheory.AutomorphicForms.L2LocalComponents.Summand
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LocStep
section
noncomputable section

open Matrix Topology

namespace UpperTheory.V.Af.Smo

section Alg

variable {R : Type} [CommRing R] {n : ℕ}

private theorem colM_mul_neg (m : Fin n) (u v : Fin n → R) (huv : u + v = 0) : colM m u * colM m v = 1 := by
  have h0 : (Matrix.of fun (i j : Fin n) => if i ≤ m ∧ j.val = m.val + 1 then u i else 0) *
      (Matrix.of fun (i j : Fin n) => if i ≤ m ∧ j.val = m.val + 1 then v i else 0) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [Matrix.of_apply]
    by_cases h1 : k ≤ m
    · have : ¬ (i ≤ m ∧ k.val = m.val + 1) := fun h => by
        have := Fin.le_def.1 h1
        omega
      rw [if_neg this, zero_mul]
    · have : ¬ (k ≤ m ∧ j.val = m.val + 1) := fun h => h1 h.1
      rw [if_neg this, mul_zero]
  unfold colM
  rw [add_mul, mul_add, mul_add, h0, one_mul, one_mul, mul_one, add_zero, add_assoc, add_eq_left]
  ext i j
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.zero_apply]
  split_ifs
  · rw [add_comm]; exact congrFun huv i
  · simp

private def colU (m : Fin n) (u : Fin n → R) : GL (Fin n) R :=
  ⟨colM m u, colM m (-u), colM_mul_neg m _ _ (by simp), colM_mul_neg m _ _ (by simp)⟩

private def dlt (m : Fin n) (ξ : Fin n → R) : (Fin n → R) →+ R where
  toFun u := dotLe m ξ u - u m
  map_zero' := by simp [dotLe]
  map_add' u v := by
    have : dotLe m ξ (u + v) = dotLe m ξ u + dotLe m ξ v := by
      unfold dotLe
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · simp [mul_add]
      · simp
    rw [this, Pi.add_apply]; ring

private theorem dlt_apply (m : Fin n) (ξ u : Fin n → R) : dlt m ξ u = dotLe m ξ u - u m := rfl

private theorem dlt_one (m : Fin n) (u : Fin n → R) : dlt m ((1 : Matrix (Fin n) (Fin n) R) m) u = 0 := by
  rw [dlt_apply, sub_eq_zero]
  unfold dotLe
  rw [Finset.sum_eq_single m]
  · simp
  · intro j _ hj
    simp [Matrix.one_apply_ne hj.symm]
  · simp

private theorem dlt_single (m : Fin n) (ξ : Fin n → R) (j : Fin n) (hj : j ≤ m) (y : R) :
    dlt m ξ (Pi.single j y) = (ξ j - (1 : Matrix (Fin n) (Fin n) R) m j) * y := by
  rw [dlt_apply]
  unfold dotLe
  rw [Finset.sum_eq_single j]
  · by_cases h : m = j
    · subst h; simp [sub_mul]
    · simp [hj, Matrix.one_apply_ne h, Pi.single_eq_of_ne h]
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

end Alg

section Top

variable {K : Type} [NormedField K] [CompleteSpace K] {n : ℕ}

private theorem img_nhds (U : OpenSubgroup (GL (Fin n) K)) :
    {M : Matrix (Fin n) (Fin n) K | ∃ s ∈ U, s.val = M} ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) K) := by
  letI I := Matrix.linftyOpNormedRing (n := Fin n) (α := K)
  have hcs : @CompleteSpace (Matrix (Fin n) (Fin n) K) I.toMetricSpace.toPseudoMetricSpace.toUniformSpace :=
    inferInstanceAs (CompleteSpace (Fin n → Fin n → K))
  have h := (@Units.isOpenMap_val (Matrix (Fin n) (Fin n) K) I
    (@instHasSummableGeomSeriesOfCompleteSpace _ (@NormedRing.toNonUnitalNormedRing _ I) hcs)) _ U.isOpen
  exact h.mem_nhds ⟨1, U.one_mem, rfl⟩

private theorem col_nhds (m : Fin n) (U : OpenSubgroup (GL (Fin n) K)) :
    ∀ᶠ u in 𝓝 (0 : Fin n → K), ∃ s ∈ U, s.val = colM m u := by
  have hc : Continuous fun u : Fin n → K => colM m u := by
    unfold colM
    refine continuous_const.add (continuous_matrix fun i j => ?_)
    simp only [Matrix.of_apply]
    split_ifs
    · exact continuous_apply i
    · exact continuous_const
  have h0 : colM m (0 : Fin n → K) = 1 := by
    ext i j; simp [colM]
  have := hc.continuousAt (x := 0)
  rw [ContinuousAt, h0] at this
  exact this (img_nhds U)

private theorem row_nhds (m : Fin n) (U : OpenSubgroup (GL (Fin n) K)) :
    ∃ V ∈ 𝓝 (0 : K), ∀ ξ : Fin n → K, (∀ j, j ≤ m → ξ j - (1 : Matrix (Fin n) (Fin n) K) m j ∈ V) →
      ∃ s ∈ U, s.val = rowM m ξ := by
  have hc : Continuous fun u : Fin n → K => rowM m (u + (1 : Matrix (Fin n) (Fin n) K) m) := by
    unfold rowM
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.of_apply]
    split_ifs
    · exact (continuous_apply j).add continuous_const
    · exact continuous_const
  have h0 : rowM m ((0 : Fin n → K) + (1 : Matrix (Fin n) (Fin n) K) m) = 1 := by
    ext i j
    simp only [rowM, Matrix.of_apply, zero_add]
    split_ifs with h
    · rw [h.1]
    · rfl
  have h1 := hc.continuousAt (x := 0)
  rw [ContinuousAt, h0] at h1
  obtain ⟨ε, hε, h2⟩ := Metric.mem_nhds_iff.1 (h1 (img_nhds U))
  refine ⟨Metric.ball 0 ε, Metric.ball_mem_nhds _ hε, fun ξ hξ => ?_⟩
  have h3 : (fun j => if j ≤ m then ξ j - (1 : Matrix (Fin n) (Fin n) K) m j else 0) ∈
      Metric.ball (0 : Fin n → K) ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro j
    split_ifs with h
    · exact hξ j h
    · simpa using hε
  obtain ⟨s, hs, e⟩ := h2 h3
  refine ⟨s, hs, e.trans ?_⟩
  ext i j
  simp only [rowM, Matrix.of_apply, Pi.add_apply]
  by_cases h : i = m ∧ j ≤ m
  · simp [h]
  · rw [if_neg h, if_neg h]

private theorem step_gen (hA : AvgChar) (ψ : AddChar K ℂ) (hψ : ∀ᶠ x in 𝓝 (0 : K), ψ x = 1)
    (hD : ∀ V ∈ 𝓝 (0 : K), ∃ L : AddSubgroup K, IsOpen (L : Set K) ∧ IsCompact (L : Set K) ∧
      ∀ x, (∀ y ∈ L, ψ (x * y) = 1) → x ∈ V) (m : Fin n) (U : OpenSubgroup (GL (Fin n) K)) :
    ∃ (c : GL (Fin n) K →₀ ℂ) (h : (Fin n → K) → ℂ),
      h ((1 : Matrix (Fin n) (Fin n) K) m) = 1 ∧ (∀ ξ, h ξ ≠ 0 → ∃ s ∈ U, s.val = rowM m ξ) ∧
      ∀ W : GL (Fin n) K → ℂ, (∀ g, ∀ u ∈ U, W (g * u) = W g) → ∀ p ξ,
        (∀ u (t : GL (Fin n) K), t.val = colM m u → W (p * t) = ψ (dotLe m ξ u) * W p) →
        comb c W p = h ξ * W p := by
  classical
  obtain ⟨V, hV, hrow⟩ := row_nhds m U
  obtain ⟨L₁, ho, hc, hL₁⟩ := hD V hV
  let L : AddSubgroup (Fin n → K) := AddSubgroup.pi Set.univ fun _ => L₁
  have hLo : IsOpen (L : Set (Fin n → K)) := isOpen_set_pi Set.finite_univ fun _ _ => ho
  have hLc : IsCompact (L : Set (Fin n → K)) := isCompact_univ_pi fun _ => hc
  let N : Set (Fin n → K) := {u | u ∈ L ∧ (∃ s ∈ U, s.val = colM m u) ∧ ψ (u m) = 1}
  have hN : N ∈ 𝓝 (0 : Fin n → K) := by
    have hψm : ∀ᶠ u in 𝓝 (0 : Fin n → K), ψ (u m) = 1 :=
      (continuous_apply m).continuousAt (x := (0 : Fin n → K)) hψ
    exact Filter.inter_mem (hLo.mem_nhds L.zero_mem) (Filter.inter_mem (col_nhds m U) hψm)
  let L₀ := AddSubgroup.closure N
  have hle : L₀ ≤ L := (AddSubgroup.closure_le _).2 fun u hu => hu.1
  have hL₀ : IsOpen (L₀ : Set (Fin n → K)) :=
    L₀.isOpen_of_mem_nhds (Filter.mem_of_superset hN AddSubgroup.subset_closure)
  have hidx : L₀.relIndex L ≠ 0 := by
    haveI : CompactSpace L := isCompact_iff_compactSpace.1 hLc
    have := AddSubgroup.quotient_finite_of_isOpen (L₀.addSubgroupOf L) (hL₀.preimage continuous_subtype_val)
    exact AddSubgroup.index_ne_zero_of_finite
  obtain ⟨T, hT, hTL, hsum⟩ := hA _ L₀ L hle hidx
  have hcard : (T.card : ℂ) ≠ 0 := by exact_mod_cast hT.card_pos.ne'
  refine ⟨∑ t ∈ T, Finsupp.single (colU m t) ((T.card : ℂ)⁻¹ * ψ (-t m)),
    fun ξ => if ∀ u ∈ L, ψ (dlt m ξ u) = 1 then 1 else 0, ?_, fun ξ hξ => ?_, fun W hW p ξ hp => ?_⟩
  · simp [dlt_one]
  · have h1 : ∀ u ∈ L, ψ (dlt m ξ u) = 1 := by
      by_contra h
      exact hξ (if_neg h)
    refine hrow ξ fun j hj => hL₁ _ fun y hy => ?_
    rw [← dlt_single m ξ j hj]
    refine h1 _ fun k _ => ?_
    by_cases h : k = j
    · subst h; simpa using hy
    · rw [Pi.single_eq_of_ne h]; exact L₁.zero_mem
  · have e1 : comb (∑ t ∈ T, Finsupp.single (colU m t) ((T.card : ℂ)⁻¹ * ψ (-t m))) W p =
        (T.card : ℂ)⁻¹ * (∑ t ∈ T, ψ (dlt m ξ t)) * W p := by
      unfold comb
      rw [← Finsupp.sum_finsetSum_index (by simp) (by intros; ring), Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finsupp.sum_single_index (by simp), hp t (colU m t) rfl, dlt_apply, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    rw [e1]
    by_cases h0 : W p = 0
    · simp [h0]
    congr 1
    dsimp only
    split_ifs with h
    · rw [Finset.sum_congr rfl fun t ht => h t (hTL t ht)]
      simp [hcard]
    · push Not at h
      have h2 : ∀ x ∈ L₀, ψ.compAddMonoidHom (dlt m ξ) x = 1 := by
        intro x hx
        induction hx using AddSubgroup.closure_induction with
        | mem u hu =>
          obtain ⟨-, ⟨s, hs, e⟩, h3⟩ := hu
          have h4 := hp u s e
          rw [hW p s hs] at h4
          have h5 : ψ (dotLe m ξ u) = 1 := mul_right_cancel₀ h0 (by rw [← h4, one_mul])
          rw [AddChar.compAddMonoidHom_apply, dlt_apply, AddChar.map_sub_eq_div, h5, h3, div_one]
        | zero => simp
        | add x y _ _ hx hy => rw [AddChar.map_add_eq_mul, hx, hy, one_mul]
        | neg x _ hx => rw [AddChar.map_neg_eq_inv, hx, inv_one]
      have := hsum _ h2 h
      simp only [AddChar.compAddMonoidHom_apply] at this
      rw [this, mul_zero]

end Top

end UpperTheory.V.Af.Smo

theorem UpperTheory.V.Af.Smo.locStep :
    UpperTheory.V.Af.Smo.AvgChar → UpperTheory.V.Af.Smo.LocDual → UpperTheory.V.Af.Smo.LocStep := by
  intro hA hD E _ _ w ψ hψ h1 n m _ U
  exact UpperTheory.V.Af.Smo.step_gen hA ψ hψ (hD E w ψ h1) m U
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.OrthTr
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

open CuspidalSpectrum RightCosetSpace in
private theorem UpperTheory.V.Af.Smo.coeFn_tr {E : Type} [Field E] [NumberField E] {n : ℕ}
    (μ : Measure (Reduction.normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] {φ : cuspForms E n} (hφ : φ ∈ centralCuspForms E n)
    (g : AdelicGLn.AdelicGL E n) :
    (toLp μ (cuspRepT μ (toOne g) (cuspVecL μ φ)) : RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)) → ℂ)
      =ᵐ[quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ] quotTr φ g := by
  rw [toLp_cuspRepT, rightRegularRep_apply, toLp_cuspVecL, quotTr_eq_comp hφ, quotTr_one]
  refine (coeFn_rightTranslate _ μ _ _).trans ?_
  exact (measurePreserving_rightMul μ (toOne g)).quasiMeasurePreserving.ae_eq (coeFn_cuspToL2 μ φ)

private theorem UpperTheory.V.Af.Smo.inner_closure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {S T : Submodule ℂ H} (h : ∀ x ∈ S, ∀ y ∈ T, inner ℂ x y = 0) {x y : H}
    (hx : x ∈ S.topologicalClosure) (hy : y ∈ T.topologicalClosure) : inner ℂ x y = 0 := by
  have h1 : T ≤ S.topologicalClosureᗮ := by
    rw [Submodule.orthogonal_closure]
    exact fun b hb => (Submodule.mem_orthogonal _ _).2 fun a ha => h a ha b hb
  exact (Submodule.mem_orthogonal _ _).1
    (Submodule.topologicalClosure_minimal T h1 (Submodule.isClosed_orthogonal _) hy) x hx

open CuspidalSpectrum RightCosetSpace in
theorem UpperTheory.V.Af.Smo.orthTr :
    UpperTheory.V.Af.Smo.OrthTr := by
  intro E _ _ n μ _ U U' hU hU' sU sU' h φ hφ φ' hφ' g g'
  have i1 := isInvariant_topologicalClosure_map μ hU sU.ρ sU.σ sU.τ
  have i2 := isInvariant_topologicalClosure_map μ hU' sU'.ρ sU'.σ sU'.τ
  have m1 := i1 (toOne g) _ (Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem (f := cuspVecL μ) hφ))
  have m2 := i2 (toOne g') _ (Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem (f := cuspVecL μ) hφ'))
  have h0 := UpperTheory.V.Af.Smo.inner_closure (by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact h a ha b hb) m1 m2
  have h1 : inner ℂ (toLp μ (cuspRepT μ (toOne g) (cuspVecL μ φ)))
      (toLp μ (cuspRepT μ (toOne g') (cuspVecL μ φ'))) = 0 := h0
  rw [MeasureTheory.L2.inner_def] at h1
  rw [← h1]
  refine integral_congr_ae ?_
  filter_upwards [UpperTheory.V.Af.Smo.coeFn_tr μ (hU hφ) g, UpperTheory.V.Af.Smo.coeFn_tr μ (hU' hφ') g'] with q e1 e2
  rw [e1, e2, RCLike.inner_apply']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.PftDeriv
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem exists_one_add_norm_pow_mul_norm_schwartz_le {V M E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : 𝓢(V × M, E)) (k : ℕ) :
    ∃ C, ∀ ξ m, (1 + ‖ξ‖) ^ k * ‖H (ξ, m)‖ ≤ C := by
  refine ⟨2 ^ k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) H, fun ξ m => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl H (ξ, m)
  rw [norm_iteratedFDeriv_zero] at h
  refine le_trans ?_ h
  gcongr
  exact norm_fst_le (ξ, m)

theorem UpperTheory.V.Af.Smo.pftDeriv :
    UpperTheory.V.Af.Smo.PftDeriv := by
  intro V M _ _ _ _ _ _ _ _ G
  obtain ⟨C0, hC0⟩ := exists_one_add_norm_pow_mul_norm_schwartz_le G (Module.finrank ℝ V + 2)
  obtain ⟨C1, hC1⟩ := exists_one_add_norm_pow_mul_norm_schwartz_le (SchwartzMap.fderivCLM ℝ (V × M) ℂ G) (Module.finrank ℝ V + 1)
  simp only [SchwartzMap.fderivCLM_apply] at hC1
  have hC0n : 0 ≤ C0 := le_trans (by positivity) (hC0 0 0)
  have hC1n : 0 ≤ C1 := le_trans (by positivity) (hC1 0 0)
  have hG0 : Continuous (⇑G) := G.continuous
  have hG1 : Continuous (fun p => fderiv ℝ (⇑G) p) :=
    (SchwartzMap.fderivCLM ℝ (V × M) ℂ G).continuous
  obtain ⟨B, hB⟩ : ∃ B : V → ℝ, ∀ ξ,
      B ξ = (C1 + 2 * Real.pi * C0) / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) := ⟨_, fun _ => rfl⟩
  have hBint : Integrable B := by
    have h := (integrable_one_add_norm (E := V) (μ := volume)
      (r := ((Module.finrank ℝ V + 1 : ℕ) : ℝ)) (by push_cast; linarith)).const_mul (C1 + 2 * Real.pi * C0)
    refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hB]
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, div_eq_mul_inv]
  have hGB : ∀ ξ m, ‖G (ξ, m)‖ ≤ B ξ := by
    intro ξ m
    rw [hB, le_div_iff₀ (by positivity)]
    calc ‖G (ξ, m)‖ * (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1)
        ≤ (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 2) * ‖G (ξ, m)‖ := by
          have : (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) ≤ (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 2) :=
            pow_le_pow_right₀ (by linarith [norm_nonneg ξ]) (by omega)
          nlinarith [norm_nonneg (G (ξ, m))]
      _ ≤ C0 := hC0 ξ m
      _ ≤ C1 + 2 * Real.pi * C0 := by nlinarith [Real.pi_gt_three]
  obtain ⟨F', hF'⟩ : ∃ F' : V × M → V → (V × M →L[ℝ] ℂ), ∀ z ξ, F' z ξ =
      ((𝐞 (-⟪ξ, z.1⟫) : Circle) : ℂ) • ((fderiv ℝ G (ξ, z.2)).comp
        ((0 : V × M →L[ℝ] V).prod (ContinuousLinearMap.snd ℝ V M))) +
      G (ξ, z.2) • ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (2 * (Real.pi : ℂ) * Complex.I * 𝐞 (-⟪ξ, z.1⟫))).comp
        (-((innerSL ℝ ξ).comp (ContinuousLinearMap.fst ℝ V M)))) := ⟨_, fun _ _ => rfl⟩
  have hF'v : ∀ z ξ v, F' z ξ v = (𝐞 (-⟪ξ, z.1⟫) : ℂ) * fderiv ℝ G (ξ, z.2) (0, v.2) +
      G (ξ, z.2) * (-((⟪ξ, v.1⟫ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * 𝐞 (-⟪ξ, z.1⟫))) := by
    intro z ξ v
    rw [hF']
    simp [Complex.real_smul]
  have hcont : ∀ z, Continuous (F' z) := by
    intro z
    have he : Continuous (fun ξ : V => ((𝐞 (-⟪ξ, z.1⟫) : Circle) : ℂ)) := by fun_prop
    have : F' z = fun ξ => _ := funext (hF' z)
    rw [this]
    fun_prop
  have hbound : ∀ z ξ, ‖F' z ξ‖ ≤ B ξ := by
    intro z ξ
    have ht : 0 < 1 + ‖ξ‖ := by positivity
    have ha : ‖fderiv ℝ G (ξ, z.2)‖ ≤ C1 / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) := by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact hC1 ξ z.2
    have hb : ‖G (ξ, z.2)‖ * ‖ξ‖ ≤ C0 / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) := by
      rw [le_div_iff₀ (by positivity)]
      calc ‖G (ξ, z.2)‖ * ‖ξ‖ * (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1)
          ≤ ‖G (ξ, z.2)‖ * (1 + ‖ξ‖) * (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) := by
            gcongr
            linarith
        _ = (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 2) * ‖G (ξ, z.2)‖ := by ring
        _ ≤ C0 := hC0 ξ z.2
    rw [hB]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [hF'v]
    have h0v : ‖((0 : V), v.2)‖ ≤ ‖v‖ := by
      rw [Prod.norm_def, Prod.norm_def]
      simp
    have h1 : ‖fderiv ℝ G (ξ, z.2) (0, v.2)‖ ≤ ‖fderiv ℝ G (ξ, z.2)‖ * ‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
    have h2 : |⟪ξ, v.1⟫| ≤ ‖ξ‖ * ‖v‖ :=
      (abs_real_inner_le_norm _ _).trans (by gcongr; exact norm_fst_le v)
    have e1 : ‖(𝐞 (-⟪ξ, z.1⟫) : ℂ) * fderiv ℝ G (ξ, z.2) (0, v.2)‖
        = ‖fderiv ℝ G (ξ, z.2) (0, v.2)‖ := by
      rw [norm_mul, Circle.norm_coe, one_mul]
    have e2 : ‖G (ξ, z.2) * (-((⟪ξ, v.1⟫ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * 𝐞 (-⟪ξ, z.1⟫)))‖
        = ‖G (ξ, z.2)‖ * (|⟪ξ, v.1⟫| * (2 * Real.pi)) := by
      simp [abs_of_pos Real.pi_pos, Circle.norm_coe]
    have h3 := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ ‖v‖ * (2 * Real.pi))
    have h4 := mul_le_mul_of_nonneg_right ha (norm_nonneg v)
    calc _ ≤ ‖fderiv ℝ G (ξ, z.2)‖ * ‖v‖ + ‖G (ξ, z.2)‖ * (‖ξ‖ * ‖v‖ * (2 * Real.pi)) := by
          refine (norm_add_le _ _).trans ?_
          rw [e1, e2]
          exact add_le_add h1 (by gcongr)
      _ ≤ (C1 + 2 * Real.pi * C0) / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) * ‖v‖ := by
          have e3 : (C1 + 2 * Real.pi * C0) / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) * ‖v‖
              = C1 / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) * ‖v‖
                + C0 / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) * (‖v‖ * (2 * Real.pi)) := by ring
          rw [e3]
          nlinarith [h3, h4]
  have hFint : ∀ z, Integrable (F' z) :=
    fun z => hBint.mono' (hcont z).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => hbound z ξ)
  have hder1 : ∀ ξ z, HasFDerivAt (fun z : V × M => (𝐞 (-⟪ξ, z.1⟫) : ℂ) * G (ξ, z.2)) (F' z ξ) z := by
    intro ξ z
    have h1 := (Real.hasDerivAt_fourierChar _).hasFDerivAt.comp z
      (((innerSL ℝ ξ).comp (ContinuousLinearMap.fst ℝ V M)).hasFDerivAt.neg)
    have h2 : HasFDerivAt (fun z : V × M => G (ξ, z.2))
        ((fderiv ℝ G (ξ, z.2)).comp ((0 : V × M →L[ℝ] V).prod (ContinuousLinearMap.snd ℝ V M))) z :=
      (G.hasFDerivAt (ξ, z.2)).comp z ((hasFDerivAt_const ξ z).prodMk hasFDerivAt_snd)
    rw [hF']
    refine ((h1.mul h2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)).congr_fderiv ?_
    · simp
    · refine ContinuousLinearMap.ext fun v => ?_
      simp
  have hpft : ∀ (H : V × M → ℂ) z, pft H z = ∫ ξ, (𝐞 (-⟪ξ, z.1⟫) : ℂ) * H (ξ, z.2) := by
    intro H z
    simp only [UpperTheory.V.Af.Smo.pft, Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  have hder : ∀ z, HasFDerivAt (pft ⇑G) (∫ ξ, F' z ξ) z := by
    intro z
    have hfun : pft ⇑G = fun z => ∫ ξ, (𝐞 (-⟪ξ, z.1⟫) : ℂ) * G (ξ, z.2) := funext (hpft G)
    rw [hfun]
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ) (bound := B)
      Filter.univ_mem ?_ ?_ ((hcont z).aestronglyMeasurable) ?_ hBint ?_
    · refine Filter.Eventually.of_forall fun z' => ?_
      have : Continuous fun ξ : V => (𝐞 (-⟪ξ, z'.1⟫) : ℂ) * G (ξ, z'.2) := by fun_prop
      exact this.aestronglyMeasurable
    · have : Continuous fun ξ : V => (𝐞 (-⟪ξ, z.1⟫) : ℂ) * G (ξ, z.2) := by fun_prop
      refine hBint.mono' this.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
      rw [norm_mul, Circle.norm_coe, one_mul]
      exact hGB ξ z.2
    · exact Filter.Eventually.of_forall fun ξ z' _ => hbound z' ξ
    · exact Filter.Eventually.of_forall fun ξ z' _ => hder1 ξ z'
  refine ⟨fun z => (hder z).differentiableAt, fun v => ?_⟩
  have hl := (Complex.ofRealCLM.comp ((innerSL ℝ v.1).comp
    (ContinuousLinearMap.fst ℝ V M))).hasTemperateGrowth
  obtain ⟨G', hG'⟩ : ∃ G' : 𝓢(V × M, ℂ), ∀ p : V × M,
      G' p = -(2 * (Real.pi : ℂ) * Complex.I) * ((⟪v.1, p.1⟫ : ℝ) : ℂ) * G p + fderiv ℝ G p (0, v.2) := by
    refine ⟨(-(2 * (Real.pi : ℂ) * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (⇑(Complex.ofRealCLM.comp ((innerSL ℝ v.1).comp (ContinuousLinearMap.fst ℝ V M)))) G
      + LineDeriv.lineDerivOp ((0 : V), v.2) G, fun p => ?_⟩
    simp [SchwartzMap.smulLeftCLM_apply_apply hl, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    ring
  refine ⟨G', ?_⟩
  funext z
  show fderiv ℝ (pft ⇑G) z v = pft (⇑G') z
  rw [(hder z).fderiv, ContinuousLinearMap.integral_apply (hFint z) v, hpft]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [hF'v, hG', real_inner_comm v.1 ξ]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Seed
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.seed :
    UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.Smo.SeedConv → UpperTheory.V.Af.Smo.Seed := by
  intro hW hS E _ _ _ n π hc
  have nice : ∀ φ ∈ π.V, Nice φ.1 := by
    intro φ hφ
    have hl := (π.cusp φ hφ).1.level
    rw [← Fb.map_carrier] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    refine ⟨ψ.2.1.continuous, exists_norm_le_of_mem_centralCuspForms (Fb.carrier_le_central π hc hψ),
      ψ.2.1.isLeftInvariant, ψ.2.2, ?_⟩
    let V : Subgroup (GL (Fin n) (Af E)) :=
      { carrier := {k | TR.finRep E n k (Fb.ofCusp E n ψ) = Fb.ofCusp E n ψ}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    exact ⟨⟨V, hl⟩, fun g v hv => congrFun (congrArg Subtype.val hv) g⟩
  refine ⟨nice, ?_⟩
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have N := nice φ hφ
  have hg : ∃ g, whittaker φ.1 g ≠ 0 := by
    by_contra h
    refine h0 (Subtype.ext (MultiplicityOne.eq_zero_of_whittaker_eq_zero N.cont N.left N.cusp ?_
      fun g => not_not.1 fun h' => h ⟨g, h'⟩))
    rw [Fb.finEmb_eq]
    exact N.level
  obtain ⟨g, hg⟩ := hg
  rw [← TR.infGL_mul_finGL g] at hg
  generalize GeneralLinearGroup.map (pInf E) g = y at hg
  generalize GeneralLinearGroup.map (pFin E) g = k at hg
  have hφ' := π.stable (.fin k) φ hφ
  refine ⟨_, hφ', hS E n _ (hW E n _ (nice _ hφ')).1 y ?_⟩
  have e : (TR.act (.fin k) φ).1 = fun x => φ.1 (x * finGL E n k) := rfl
  rw [e]
  simpa only [whittaker, mul_assoc] using hg
end

