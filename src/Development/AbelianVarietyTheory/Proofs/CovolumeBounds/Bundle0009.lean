module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SumFinsuppAntidiagProdPowDivMultiFactorial
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsMinorProdEqSmulColActBasePoly
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DiscreteTopologySpanOfLinearIndependent
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EventuallyExistsMulIsLowerTriangular
section
open MvPolynomial Matrix Topology Filter
open GlobalTheory.MvPoly

namespace GlobalTheory.Harm

section Adjoint

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem pderiv_algHom_of_linear {R : Type*} [CommRing R]
    (G : MvPolynomial τ R →ₐ[R] MvPolynomial σ R) (M : σ → τ → R)
    (hG : ∀ j, G (X j) = ∑ i, M i j • X i) (i : σ) (Q : MvPolynomial τ R) :
    pderiv i (G Q) = ∑ j, M i j • G (pderiv j Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C r => simp [algHom_C]
  | add P Q hP hQ => simp [hP, hQ, Finset.sum_add_distrib]
  | mul_X P k hP =>
    have h1 : pderiv i (G (X k)) = C (M i k) := by
      simp [hG, pderiv_X, Pi.single_apply, smul_eq_C_mul]
    have h2 : ∑ j, M i j • G (P * pderiv j (X k)) = G P * C (M i k) := by
      rw [Finset.sum_eq_single k]
      · simp [smul_eq_C_mul, mul_comm]
      · intro j _ hj
        simp [pderiv_X, Pi.single_apply, hj.symm]
      · simp
    rw [map_mul, Derivation.leibniz, hP, h1, smul_eq_mul, smul_eq_mul, ← h2, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Derivation.leibniz, map_add (f := _), smul_add, smul_eq_mul, smul_eq_mul, map_mul G (X k),
      mul_smul_comm]


omit [Fintype τ] in
theorem constantCoeff_algHom_of_linear {R : Type*} [CommRing R]
    (G : MvPolynomial τ R →ₐ[R] MvPolynomial σ R) (M : σ → τ → R)
    (hG : ∀ j, G (X j) = ∑ i, M i j • X i) (Q : MvPolynomial τ R) :
    constantCoeff (G Q) = constantCoeff Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp [algHom_C]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P k hP => simp [hG, smul_eq_C_mul]

theorem fockInner_algHom_of_linear (F : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ)
    (G : MvPolynomial τ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (M : σ → τ → ℂ)
    (hF : ∀ i, F (X i) = ∑ j, M i j • X j) (hG : ∀ j, G (X j) = ∑ i, star (M i j) • X i)
    (P : MvPolynomial σ ℂ) (Q : MvPolynomial τ ℂ) : fockInner (F P) Q = fockInner P (G Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C r =>
    have := constantCoeff_algHom_of_linear G _ hG Q
    rw [constantCoeff_eq] at this
    rw [algHom_C, algebraMap_eq, C_apply, C_apply, fockInner_monomial_left,
      fockInner_monomial_left, this]
    simp [constantCoeff_eq]
  | add P P' hP hP' => rw [map_add (f := _), fockInner_add_left, fockInner_add_left, hP, hP']
  | mul_X P k hP =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mul_comm P, fockInner_X_mul_left, pderiv_algHom_of_linear G _ hG, map_mul, hF,
      Finset.sum_mul, ← fockInnerₛₗ_apply, ← fockInnerₛₗ_apply, map_sum, map_sum,
      LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fockInnerₛₗ_apply, fockInnerₛₗ_apply, smul_mul_assoc, fockInner_smul_left,
      fockInner_smul_right, fockInner_X_mul_left, hP]
    simp

variable {T κ : Type*} [Fintype T] [Fintype κ] {p q : ℕ}

theorem fockInner_colSubst (A B : T → Matrix κ κ ℂ) (P Q : Poly ℂ T p q κ) :
    fockInner (colSubst A B P) Q =
      fockInner P (colSubst (fun t => (A t)ᴴ) (fun t => (B t)ᴴ) Q) := by
  classical
  refine fockInner_algHom_of_linear _ _ (fun v w => if v.1 = w.1 ∧ v.2.1 = w.2.1 then
    Sum.elim (fun _ => A v.1 v.2.2 w.2.2) (fun _ => B v.1 w.2.2 v.2.2) v.2.1 else 0) ?_ ?_ P Q
  · rintro ⟨t, a | b, k⟩
    · rw [colSubst_X_xVar, xForm_apply]
      simp [Fintype.sum_prod_type, ite_and, smul_eq_C_mul, apply_ite C]
    · rw [colSubst_X_yVar, yForm_apply]
      simp [Fintype.sum_prod_type, ite_and, smul_eq_C_mul, apply_ite C]
  · rintro ⟨t, a | b, k⟩
    · rw [colSubst_X_xVar, xForm_apply]
      simp [Fintype.sum_prod_type, ite_and, smul_eq_C_mul, apply_ite C, apply_ite star]
    · rw [colSubst_X_yVar, yForm_apply]
      simp [Fintype.sum_prod_type, ite_and, smul_eq_C_mul, apply_ite C, apply_ite star]

theorem fockInner_colAct [DecidableEq κ] (g : T → GL κ ℂ) (P Q : Poly ℂ T p q κ) :
    fockInner (colAct ℂ T p q κ g P) Q = fockInner P (colAct ℂ T p q κ (star g) Q) := by
  rw [colAct_apply, colAct_apply, fockInner_colSubst]
  rfl

theorem exists_fockInner_sub_eq_zero {σ : Type*} (W : Submodule ℂ (MvPolynomial σ ℂ))
    [FiniteDimensional ℂ W] (P : MvPolynomial σ ℂ) :
    ∃ Q ∈ W, ∀ w ∈ W, fockInner (P - Q) w = 0 := by
  let b := Module.finBasis ℂ W
  let L : MvPolynomial σ ℂ →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    LinearMap.pi fun i => (fockInnerₛₗ σ ℂ).flip (b i)
  have hL (P) (h : L P = 0) (w) (hw : w ∈ W) : fockInner P w = 0 := by
    have := congrArg W.subtype (b.sum_repr ⟨w, hw⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Submodule.subtype_apply] at this
    change _ = w at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← this, ← fockInnerₛₗ_apply, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, fockInnerₛₗ_apply, fockInner_smul_right]
    exact mul_eq_zero_of_right _ (congrFun h i)
  have hinj : Function.Injective (L ∘ₗ W.subtype) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have := hL x hx x x.2
    rw [fockInner_self] at this
    exact Subtype.ext (fockNormSq_eq_zero.mp (RCLike.ofReal_eq_zero.mp this))
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
    (L P)
  exact ⟨x, x.2, hL _ (by rw [map_sub, ← hx]; simp)⟩

end Adjoint

section Triangular

variable {R : Type*} [CommRing R] {T : Type*} [Fintype T] {p q n : ℕ}

end Triangular

section Density

variable {T κ : Type*} [Fintype κ] {p q n : ℕ}

end Density

end GlobalTheory.Harm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsNeZeroNormSqLeMulCovolumeRpow
section
noncomputable section

open Module Submodule MeasureTheory

namespace GlobalTheory

section FirstTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem measure_le_two_pow_mul_covolume (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} (hsymm : ∀ x ∈ s, -x ∈ s) (hconv : Convex ℝ s)
    (hL : ∀ x ∈ L, x ≠ 0 → x ∉ s) :
    μ s ≤ ENNReal.ofReal (2 ^ finrank ℝ E * ZLattice.covolume L μ) := by
  by_contra! hlt
  let b := Free.chooseBasis ℤ L
  have fund : IsAddFundamentalDomain L.toAddSubgroup
      (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) μ :=
    ZLattice.isAddFundamentalDomain b μ
  have hc : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain L μ
    (ZLattice.isAddFundamentalDomain b μ)
  have hfin : μ (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  obtain ⟨x, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund
    hsymm hconv (by
      rwa [← ENNReal.ofReal_toReal hfin, ← measureReal_def, ← hcov, ← ENNReal.ofReal_ofNat,
        ← ENNReal.ofReal_pow (by norm_num),
        ← ENNReal.ofReal_mul (ZLattice.covolume_pos L μ).le, mul_comm])
  exact hL x x.2 (fun h ↦ hx0 (Subtype.ext h)) hxs

end FirstTheorem

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_linearMap_det_eq_prod_inv_succMin (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    ∃ T : E →ₗ[ℝ] E, LinearMap.det T = (∏ i : Fin (finrank ℝ E), succMin L (i + 1))⁻¹ ∧
      ∀ x ∈ L, x ≠ 0 → 1 ≤ ‖T x‖ := by
  obtain ⟨b, hbL, hbN⟩ := exists_basis_norm_eq_succMin L
  have h : finrank ℝ E = Fintype.card (Fin (finrank ℝ E)) := (Fintype.card_fin _).symm
  let o := InnerProductSpace.gramSchmidtOrthonormalBasis h b
  let l : Fin (finrank ℝ E) → ℝ := fun i ↦ succMin L (i + 1)
  have hl : ∀ i, 0 < l i := fun i ↦ succMin_pos_of_isZLattice (by omega) i.2
  let T : E →ₗ[ℝ] E := Matrix.toLin o.toBasis o.toBasis (Matrix.diagonal fun i ↦ (l i)⁻¹)
  have hT : ∀ x i, o.repr (T x) i = (l i)⁻¹ * o.repr x i := by
    intro x i
    have := Matrix.repr_toLin o.toBasis o.toBasis (Matrix.diagonal fun i ↦ (l i)⁻¹) x
    have h2 := congrFun this i
    rw [Matrix.mulVec_diagonal] at h2
    exact h2
  refine ⟨T, ?_, fun x hx h0 ↦ ?_⟩
  · rw [LinearMap.det_toLin, Matrix.det_diagonal, Finset.prod_inv_distrib]
  · have hne : (Finset.univ.filter fun i ↦ o.repr x i ≠ 0).Nonempty := by
      by_contra hc
      apply h0
      apply o.repr.injective
      ext i
      simpa using (Finset.filter_eq_empty_iff.1 (Finset.not_nonempty_iff_eq_empty.1 hc)
        (Finset.mem_univ i))
    obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image _ id hne
    have hk0 : o.repr x k ≠ 0 := (Finset.mem_filter.1 hk).2
    have hspan : x ∉ span ℝ (b '' {j | (j : ℕ) < k}) := by
      intro hmem
      have hle : span ℝ (b '' {j | (j : ℕ) < k}) ≤ LinearMap.ker (o.toBasis.coord k) := by
        refine span_le.2 ?_
        rintro _ ⟨j, hj, rfl⟩
        exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular' h b
          (show j < k from hj)
      exact hk0 (hle hmem)
    have hx1 : l k ≤ ‖x‖ :=
      succMin_le_norm_of_notMem_span b.linearIndependent hbL (fun j ↦ (hbN j).le) k.2.le hx hspan
    have hcmp : ‖(l k)⁻¹ • x‖ ^ 2 ≤ ‖T x‖ ^ 2 := by
      rw [← o.repr.norm_map, ← o.repr.norm_map, EuclideanSpace.norm_sq_eq,
        EuclideanSpace.norm_sq_eq]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      rw [hT, map_smul, PiLp.smul_apply, smul_eq_mul]
      by_cases hi : o.repr x i = 0
      · simp [hi]
      · have hik : i ≤ k := hmax i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
        have hlik : l i ≤ l k :=
          succMin_mono_of_isZLattice (Nat.succ_le_succ hik) k.2
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (inv_pos.2 (hl i)).le,
          Real.norm_of_nonneg (inv_pos.2 (hl k)).le]
        have := hl i
        have := hl k
        gcongr
    refine le_trans ?_ (le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hcmp)
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 (hl k)).le, le_inv_mul_iff₀ (hl k), mul_one]
    exact hx1

variable [MeasurableSpace E] [BorelSpace E]

theorem volume_real_unitBall_pos : 0 < volume.real (Metric.ball (0 : E) 1) :=
  ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne


variable (E) in
theorem two_div_sqrt_pow_le_volume_unitBall :
    (2 / √(finrank ℝ E : ℝ)) ^ finrank ℝ E ≤ volume.real (Metric.ball (0 : E) 1) := by
  let o := stdOrthonormalBasis ℝ E
  let f : E →ₗ[ℝ] (Fin (finrank ℝ E) → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin (finrank ℝ E) → ℝ)).toLinearMap ∘ₗ o.repr.toLinearEquiv.toLinearMap
  have hf : MeasurePreserving f := (PiLp.volume_preserving_ofLp _).comp o.measurePreserving_repr
  set r : ℝ := (√(finrank ℝ E : ℝ))⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hs : volume (f ⁻¹' Metric.closedBall 0 r) = ENNReal.ofReal ((2 * r) ^ finrank ℝ E) := by
    rw [hf.measure_preimage Metric.isClosed_closedBall.measurableSet.nullMeasurableSet,
      Real.volume_pi_closedBall _ hr0, Fintype.card_fin]
  have hsub : f ⁻¹' Metric.closedBall 0 r ⊆ Metric.closedBall (0 : E) 1 := by
    intro x hx
    have hi : ∀ i, ‖o.repr x i‖ ≤ r := fun i ↦
      (pi_norm_le_iff_of_nonneg hr0).1 (mem_closedBall_zero_iff.1 hx) i
    rw [mem_closedBall_zero_iff, ← sq_le_one_iff₀ (norm_nonneg _), ← o.repr.norm_map,
      EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖o.repr x i‖ ^ 2 ≤ ∑ _i : Fin (finrank ℝ E), r ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ by have := hi i; gcongr
      _ = finrank ℝ E * (finrank ℝ E : ℝ)⁻¹ := by simp [hr]
      _ ≤ 1 := mul_inv_le_one
  have h := measure_mono (μ := volume) hsub
  rw [hs, Measure.addHaar_unitClosedBall_eq_addHaar_unitBall,
    ENNReal.ofReal_le_iff_le_toReal measure_ball_lt_top.ne] at h
  rwa [div_eq_mul_inv]


variable (E) in
theorem two_pow_div_volume_unitBall_le :
    2 ^ finrank ℝ E / volume.real (Metric.ball (0 : E) 1) ≤
      (finrank ℝ E : ℝ) ^ ((finrank ℝ E : ℝ) / 2) := by
  have h := two_div_sqrt_pow_le_volume_unitBall E
  have h2 : (finrank ℝ E : ℝ) ^ ((finrank ℝ E : ℝ) / 2) = √(finrank ℝ E : ℝ) ^ finrank ℝ E := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    congr 1; ring
  have h3 : 0 < √(finrank ℝ E : ℝ) ^ finrank ℝ E := by
    rcases Nat.eq_zero_or_pos (finrank ℝ E) with h0 | hpos
    · simp [h0]
    · positivity
  rw [div_pow, div_le_iff₀ h3] at h
  rwa [h2, div_le_iff₀ volume_real_unitBall_pos, mul_comm]

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

theorem prod_succMin_mul_volume_unitBall_le :
    (∏ i : Fin (finrank ℝ E), succMin L (i + 1)) * volume.real (Metric.ball (0 : E) 1) ≤
      2 ^ finrank ℝ E * ZLattice.covolume L := by
  obtain ⟨T, hdet, hT⟩ := exists_linearMap_det_eq_prod_inv_succMin L
  have hP : 0 < ∏ i : Fin (finrank ℝ E), succMin L (i + 1) :=
    Finset.prod_pos fun i _ ↦ succMin_pos_of_isZLattice (by omega) i.2
  have h := measure_le_two_pow_mul_covolume L volume (s := T ⁻¹' Metric.ball 0 1)
    (fun x hx ↦ by simpa using hx) ((convex_ball 0 1).linear_preimage T)
    (fun x hx h0 hs ↦ (hT x hx h0).not_gt (mem_ball_zero_iff.1 hs))
  have hc := ZLattice.covolume_pos L volume
  rw [Measure.addHaar_preimage_linearMap _ (by rw [hdet]; positivity), hdet, inv_inv,
    abs_of_pos hP, ← ofReal_measureReal measure_ball_lt_top.ne, ← ENNReal.ofReal_mul hP.le,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  exact h

theorem prod_succMin_le_two_pow_div_mul_covolume :
    ∏ i : Fin (finrank ℝ E), succMin L (i + 1) ≤
      2 ^ finrank ℝ E / volume.real (Metric.ball (0 : E) 1) * ZLattice.covolume L := by
  rw [div_mul_eq_mul_div, le_div_iff₀ volume_real_unitBall_pos]
  exact prod_succMin_mul_volume_unitBall_le L

theorem prod_succMin_le_rpow_mul_covolume :
    ∏ i : Fin (finrank ℝ E), succMin L (i + 1) ≤
      (finrank ℝ E : ℝ) ^ ((finrank ℝ E : ℝ) / 2) * ZLattice.covolume L :=
  (prod_succMin_le_two_pow_div_mul_covolume L).trans
    (mul_le_mul_of_nonneg_right (two_pow_div_volume_unitBall_le E)
      (ZLattice.covolume_pos L volume).le)

theorem succMin_mul_minNorm_pow_le {k : ℕ} (h1 : 1 ≤ k) (hk : k ≤ finrank ℝ E) :
    succMin L k * minNorm L ^ (finrank ℝ E - 1) ≤
      (finrank ℝ E : ℝ) ^ ((finrank ℝ E : ℝ) / 2) * ZLattice.covolume L := by
  refine le_trans ?_ (prod_succMin_le_rpow_mul_covolume L)
  let j : Fin (finrank ℝ E) := ⟨k - 1, by omega⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), show (j : ℕ) + 1 = k by simp [j]; omega]
  refine mul_le_mul_of_nonneg_left ?_ (succMin_nonneg L k)
  calc minNorm L ^ (finrank ℝ E - 1) = ∏ _i ∈ Finset.univ.erase j, minNorm L := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ ↦ succMin_nonneg L 1) fun i _ ↦
        succMin_mono_of_isZLattice (by omega) i.2

end Euclidean

section Discrete

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L]

theorem prod_succMin_le_rpow_mul_spanCovol :
    ∏ i : Fin (finrank ℤ L), succMin L (i + 1) ≤
      (finrank ℤ L : ℝ) ^ ((finrank ℤ L : ℝ) / 2) * spanCovol L := by
  borelize E
  have h := prod_succMin_le_rpow_mul_covolume (inSpan L)
  simp only [succMin_inSpan] at h
  rw [spanCovol_eq_covolume_comap_span, ← finrank_span_eq_finrank_int]
  exact h

end Discrete

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
section
open Complex Matrix Filter Topology
open scoped Real

noncomputable section

namespace GlobalTheory

variable {ι : Type*} [Fintype ι]

def riemannThetaJointForm (a : ι → ℝ) (n : ι → ℤ) : ((ι → ℂ) × (ι → ι → ℂ)) →L[ℂ] ℂ :=
  (riemannThetaForm a n).coprod (∑ i, ∑ j, (π * I * (((n i : ℂ) + a i) * ((n j : ℂ) + a j))) •
    (ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ι → ℂ) i))

@[simp] theorem riemannThetaJointForm_apply (a : ι → ℝ) (n : ι → ℤ)
    (p : (ι → ℂ) × (ι → ι → ℂ)) :
    riemannThetaJointForm a n p =
      2 * π * I * (((fun i => (n i : ℂ) + a i) ⬝ᵥ (of p.2 *ᵥ fun i => (n i : ℂ) + a i)) / 2 +
        (fun i => (n i : ℂ) + a i) ⬝ᵥ p.1) := by
  obtain ⟨w, A⟩ := p
  have : ∑ i, ∑ j, π * I * (((n i : ℂ) + a i) * ((n j : ℂ) + a j)) * A i j =
      π * I * ((fun i => (n i : ℂ) + a i) ⬝ᵥ (of A *ᵥ fun i => (n i : ℂ) + a i)) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, of_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [riemannThetaJointForm, ContinuousLinearMap.coprod_apply, riemannThetaForm_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, this]
  ring

theorem riemannThetaTerm_eq_cexp_jointForm (a b : ι → ℝ) (n : ι → ℤ)
    (p : (ι → ℂ) × (ι → ι → ℂ)) :
    riemannThetaTerm a b (of p.2) p.1 n =
      cexp (riemannThetaJointForm a n p + riemannThetaForm a n fun i => (b i : ℂ)) := by
  have : (fun i => p.1 i + (b i : ℂ)) = p.1 + fun i => (b i : ℂ) := rfl
  rw [riemannThetaTerm, riemannThetaJointForm_apply, riemannThetaForm_apply, this, dotProduct_add]
  congr 1
  ring

theorem differentiable_riemannThetaTerm (a b : ι → ℝ) (n : ι → ℤ) :
    Differentiable ℂ fun p : (ι → ℂ) × (ι → ι → ℂ) => riemannThetaTerm a b (of p.2) p.1 n := by
  simp only [riemannThetaTerm_eq_cexp_jointForm]
  fun_prop

theorem IsSiegel.exists_isOpen_norm_riemannThetaTerm_le {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) : ∃ U : Set ((ι → ℂ) × (ι → ι → ℂ)), IsOpen U ∧ (v, of.symm Ω) ∈ U ∧
      ∃ u : (ι → ℤ) → ℝ, Summable u ∧
        ∀ n, ∀ p ∈ U, ‖riemannThetaTerm a b (of p.2) p.1 n‖ ≤ u n := by
  obtain ⟨c, hc, S, hS⟩ := h.exists_eventually_norm_riemannThetaTerm_le a b v
  obtain ⟨U, hU, hUo, hp⟩ := _root_.eventually_nhds_iff.mp hS
  exact ⟨U, hUo, hp, _, summable_riemannThetaBound a hc S, fun n p hp => hU p hp n⟩

theorem IsSiegel.analyticAt_riemannTheta_entries {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) :
    AnalyticAt ℂ (fun p : (ι → ℂ) × (ι → ι → ℂ) => riemannTheta a b (of p.2) p.1)
      (v, of.symm Ω) := by
  obtain ⟨U, hU, hp, u, hu, hle⟩ := h.exists_isOpen_norm_riemannThetaTerm_le a b v
  exact SCV.analyticAt_of_differentiableOn (SCV.differentiableOn_tsum_of_locally_normal hU
    (fun n => (differentiable_riemannThetaTerm a b n).differentiableOn)
    fun x hx => ⟨U, hU.mem_nhds hx, u, hu, hle⟩) (hU.mem_nhds hp)

section Families

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem differentiableOn_riemannTheta_comp (a b : ι → ℝ) {Ω : E → Matrix ι ι ℂ} {v : E → ι → ℂ}
    {U : Set E} (h : ∀ x ∈ U, IsSiegel (Ω x)) (hΩ : ∀ i j, DifferentiableOn ℂ (fun y => Ω y i j) U)
    (hv : DifferentiableOn ℂ v U) :
    DifferentiableOn ℂ (fun y => riemannTheta a b (Ω y) (v y)) U := fun x hx =>
  ((h x hx).analyticAt_riemannTheta_entries a b (v x)).differentiableAt.comp_differentiableWithinAt
    (f := fun y => (v y, of.symm (Ω y))) x
    ((hv x hx).prodMk
      (differentiableWithinAt_pi.mpr fun i => differentiableWithinAt_pi.mpr fun j => hΩ i j x hx))

end Families

section Upper

variable {ι : Type*} [LinearOrder ι]

variable [Fintype ι]

end Upper

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
section
open Filter Topology

namespace GlobalTheory

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem norm_pderivIter_le_of_nonneg {F : (ι → ℂ) → V} {U : Set (ι → ℂ)} {a : ι → ℂ} {r : ι → ℝ}
    {M : ℝ} (α : ι →₀ ℕ) (hr : ∀ k, 0 ≤ r k) (hα : ∀ k, α k ≠ 0 → 0 < r k) (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hsub : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ ≤ r k) → z ∈ U)
    (hM : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ = r k) → ‖F z‖ ≤ M) :
    ‖pderivIter α F a‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, r k ^ α k :=
  norm_pderivIter_le_of_analyticAt α hr hα
    (fun z hz => SCV.analyticOnNhd_of_differentiableOn hU hF z (hsub z hz)) hM

theorem norm_pderivIter_le_of_differentiable {F : (ι → ℂ) → V} {a : ι → ℂ} {r : ι → ℝ} {M : ℝ}
    (α : ι →₀ ℕ) (hr : ∀ k, 0 ≤ r k) (hα : ∀ k, α k ≠ 0 → 0 < r k) (hF : Differentiable ℂ F)
    (hM : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ = r k) → ‖F z‖ ≤ M) :
    ‖pderivIter α F a‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, r k ^ α k :=
  norm_pderivIter_le_of_nonneg α hr hα isOpen_univ hF.differentiableOn
    (fun _ _ => Set.mem_univ _) hM

section Holomorphic

variable {F G : (ι → ℂ) → V} {U : Set (ι → ℂ)} {a : ι → ℂ}

end Holomorphic

end GlobalTheory
end

