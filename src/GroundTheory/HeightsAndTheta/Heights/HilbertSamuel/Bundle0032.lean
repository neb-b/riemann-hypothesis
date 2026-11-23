module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNonvanishingDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem NonvanishingDense.aeval_map_rat {σ : Type} (z : σ → ℂ) (g : MvPolynomial σ ℤ) :
    aeval z (map (Int.castRingHom ℚ) g) = eval z (map (Int.castRingHom ℂ) g) := by
  rw [aeval_def, eval₂_map, eval_map]
  congr 1

theorem NonvanishingDense.proof (h : RatPrimeDense.Statement) : NonvanishingDense.Statement := by
  intro K _ ι _ P d f hP hf z hz
  obtain ⟨_, ⟨hprime, -, -⟩, hhor, -⟩ := hP
  let _ : Algebra (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) := algebraMvPolynomial
  have hφ : ∀ g, algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) g =
      map (Int.castRingHom ℚ) g := fun g => by
    change map (algebraMap ℤ ℚ) g = _
    congr 1
  have hdisj : Disjoint ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)) : Set (MRing ι)) ↑P := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, hn, rfl⟩ hnP
    have : n ∈ P.comap (C : ℤ →+* MRing ι) := hnP
    rw [hhor, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hn this
  set Pq := Ideal.map (algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ)) P
  have hPq : Pq.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint ((nonZeroDivisors ℤ).map C) _ P hprime hdisj
  have hunder : Pq.comap (algebraMap _ _) = P :=
    IsLocalization.under_map_of_isPrime_disjoint ((nonZeroDivisors ℤ).map C) _ hprime hdisj
  have hfq : map (Int.castRingHom ℚ) f ∉ Pq := fun h' => hf (by
    rw [← hunder, Ideal.mem_comap, hφ]; exact h')

  have hzero : ∀ w : (Σ k, ι k) → ℂ, (∀ g ∈ P, eval w (map (Int.castRingHom ℂ) g) = 0) →
      ∀ g ∈ Pq, aeval w g = 0 := by
    intro w hw g hg
    have hle : Pq ≤ RingHom.ker (aeval w : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] ℂ).toRingHom := by
      refine Ideal.map_le_iff_le_comap.mpr fun g' hg' => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, hφ]
      change aeval w (map (Int.castRingHom ℚ) g') = 0
      rw [NonvanishingDense.aeval_map_rat]
      exact hw g' hg'
    exact hle hg
  have hz' : z ∈ closure {w : (Σ k, ι k) → ℂ | (∀ g ∈ Pq, aeval w g = 0) ∧
      aeval w (map (Int.castRingHom ℚ) f) ≠ 0} := h _ Pq _ hPq hfq (hzero z hz.2)
  have hU : IsOpen {w : (Σ k, ι k) → ℂ | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  refine closure_mono ?_ (hU.inter_closure ⟨hz.1, hz'⟩)
  rintro w ⟨hwU, hwP, hwf⟩
  refine ⟨⟨hwU, fun g hg => ?_⟩, ?_⟩
  · rw [← NonvanishingDense.aeval_map_rat, ← hφ]
    exact hwP _ (Ideal.mem_map_of_mem _ hg)
  · rwa [← NonvanishingDense.aeval_map_rat]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPointHeightFS
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace PointHeightFSAux

abbrev fsOne : HermLine (GlobalTheory (Fin 1)) := HermLine.ofCone (fsMetric (ι := Ix (Fin 1)))

abbrev x0 : MRing (GlobalTheory (Fin 1)) := X ⟨(), 0⟩

theorem isSmoothHerm_fsOne : IsSmoothHerm fsOne := by
  refine (ProjLine.isSmoothMetric_fs (J := Ix (Fin 1))).mono fun z hz h0 => ?_
  obtain ⟨i, hi⟩ := hz ()
  exact hi (congrFun h0 _)

theorem divisorSupport_coordinate_point : divSupp (⊥ : Ideal (MRing (GlobalTheory (Fin 1)))) x0 = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun W hW => ?_
  obtain ⟨i, hi⟩ := hW.2 ()
  have hle := hW.1.1.2
  have hi0 : i = 0 := Subsingleton.elim _ _
  subst hi0
  exact hi (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))

theorem logNorm_coordinate_point : logNorm fsOne x0 = fun _ => 0 := by
  funext z
  have hρ : fsOne.h z = ‖z ⟨(), 0⟩‖ := by
    let _ : Unique (Ix (Fin 1)) :=
      ⟨⟨⟨(), 0⟩⟩, fun p => by rcases p with ⟨⟨⟩, i⟩; rw [Subsingleton.elim i 0]; rfl⟩
    show ‖WithLp.toLp 2 z‖ = _
    rw [EuclideanSpace.norm_eq, Fintype.sum_unique, Real.sqrt_sq (norm_nonneg _)]
    rfl
  simp only [logNorm, hρ, map_X, eval_X]
  rcases eq_or_ne (z ⟨(), 0⟩) 0 with h | h
  · simp [h]
  · rw [div_self (norm_ne_zero_iff.mpr h), Real.log_one]

theorem ptsIntegral_zero {e : ℕ} (P : Ideal (MRing (GlobalTheory (Fin 1))))
    (φ : Fin e → (Ix (Fin 1) → ℂ) → ℝ) : ptsIntegral P φ (fun _ => 0) = 0 := by
  classical
  unfold ptsIntegral
  split_ifs
  · simp [ptsIntegralAt, sheetDensity]
  · rfl

end PointHeightFSAux


open PointHeightFSAux in
theorem PointHeightFS.proof : PointHeightFS.Statement := by
  intro I hI
  classical
  have hP : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (Fin 1)))) (0 + 1) := IndefiniteRowSideFullHecke.Inter.isArithVar_bot 0
  have hs : IsMultiHomog x0 fun _ => 1 := IndefiniteRowSideFullHecke.Inter.isMultiHomog_Xb 1 0
  have hx0 : x0 ∉ (⊥ : Ideal (MRing (GlobalTheory (Fin 1)))) := by
    rw [Ideal.mem_bot]
    exact X_ne_zero _
  have hR := (hI Unit (GlobalTheory (Fin 1))).2.2 ⊥ 0 Fin.elim0 fsOne x0 (fun _ => 1) hP (fun j => j.elim0)
    isSmoothHerm_fsOne (fun _ => rfl) hs hx0
  have hL : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine (GlobalTheory (Fin 1))) fsOne : Fin 1 → _) =
      fun _ => fsOne := by
    funext j
    fin_cases j
    rfl
  rw [hL] at hR
  unfold hhOf
  rw [hR, recR, divisorSupport_coordinate_point, finsum_mem_empty, zero_sub, arInt, logNorm_coordinate_point, ptsIntegral_zero, neg_zero]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolydiscSubmean
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Metric Real

noncomputable section

theorem integral_polydisc_gauss (D n : ℕ) (lam : Fin D → ℝ) (R : ℝ) (hn : 0 < n) (hR : 0 < R) :
    ∫ z in closedBall (0 : Fin D → ℂ) (R / Real.sqrt n),
        Real.exp (-(n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2) =
      ((n : ℝ) ^ D)⁻¹ * ∏ j, gaussDiscMass (lam j) R := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hρ : 0 < R / Real.sqrt n := div_pos hR (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have hsq : (R / Real.sqrt n) ^ 2 = R ^ 2 / n := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hball : closedBall (0 : Fin D → ℂ) (R / Real.sqrt n) =
      Set.univ.pi fun _ => closedBall (0 : ℂ) (R / Real.sqrt n) := by
    rw [closedBall_pi _ hρ.le]
    rfl
  have hw : ∀ z : Fin D → ℂ, Real.exp (-(n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2) =
      ∏ j, Real.exp (-((n : ℝ) * lam j) * ‖z j‖ ^ 2) := by
    intro z
    rw [← Real.exp_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hfac : ∀ j, ∫ x in closedBall (0 : ℂ) (R / Real.sqrt n),
      Real.exp (-((n : ℝ) * lam j) * ‖x‖ ^ 2) = gaussDiscMass (lam j) R * (n : ℝ)⁻¹ := by
    intro j
    rw [integral_closedBall_gauss _ _ hρ.le, gaussDiscMass]
    by_cases hl : lam j = 0
    · rw [if_pos (by simp [hl]), if_pos hl, hsq]
      ring
    · have hnl : (n : ℝ) * lam j ≠ 0 := mul_ne_zero hn' hl
      rw [if_neg hnl, if_neg hl, hsq]
      have e : -((n : ℝ) * lam j) * (R ^ 2 / n) = -lam j * R ^ 2 := by
        field_simp
      rw [e]
      field_simp
  simp_rw [hw]
  rw [hball, volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod
    (fun (j : Fin D) (x : ℂ) => Real.exp (-((n : ℝ) * lam j) * ‖x‖ ^ 2))]
  simp_rw [hfac]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow,
    mul_comm]

theorem PolydiscSubmean.proof : PolydiscSubmean.Statement := by
  intro D n lam R f hn hR _ hf
  set w : (Fin D → ℂ) → ℝ := fun z => Real.exp (-(n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2) with hwdef
  have hwc : Continuous w := by
    rw [hwdef]
    fun_prop
  have hw0 : ∀ z, 0 ≤ w z := fun z => (Real.exp_pos _).le
  have hrot : ∀ (u : Circle) z, w ((u : ℂ) • z) = w z := by
    intro u z
    simp only [hwdef, Pi.smul_apply, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
  have h := sq_norm_mul_setIntegral_le hf hwc hw0 hrot
  simp only [hwdef] at h
  rw [integral_polydisc_gauss D n lam R hn hR, ← mul_assoc] at h
  exact h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PReductionToProjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

namespace ReductionToProjective

theorem powLog_shift_le (D : ℕ) {n j : ℕ} (hj : j ≤ n) :
    ((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1) ≤
      2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
  have h1 := powLog_mono D (show n + j ≤ 2 * n by omega)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2 : 2 * Real.log ((n : ℝ) + 1) = Real.log (((n : ℝ) + 1) ^ 2) := by
    rw [Real.log_pow]; push_cast; ring
  have hlog : Real.log (((2 * n : ℕ) : ℝ) + 1) ≤ 2 * Real.log ((n : ℝ) + 1) := by
    rw [h2]
    exact Real.log_le_log (by positivity) (by push_cast; nlinarith)
  have hp : ((2 * n : ℕ) : ℝ) ^ D = 2 ^ D * (n : ℝ) ^ D := by push_cast; rw [mul_pow]
  calc ((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1)
      ≤ ((2 * n : ℕ) : ℝ) ^ D * Real.log (((2 * n : ℕ) : ℝ) + 1) := h1
    _ ≤ ((2 * n : ℕ) : ℝ) ^ D * (2 * Real.log ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by rw [hp]; ring

theorem sub_chiP_isBigO (D k : ℕ) (δ C : ℝ) (hδ : 0 ≤ δ) (chi : ℕ → ℝ)
    (hlo : ∀ n : ℕ, k + 1 ≤ n → δ * chiP D (n - k) - C * (n : ℝ) ^ D * Real.log (n + 1) ≤ chi n)
    (hhi : ∀ n : ℕ, k + 1 ≤ n → chi n ≤ δ * chiP D (n + k) + C * (n : ℝ) ^ D * Real.log (n + 1)) :
    (fun n => chi n - δ * chiP D n) =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  obtain ⟨C', hC'⟩ := exists_chiP_succ_sub_le D
  refine IsBigO.of_bound (δ * (k * (|C'| * 2 ^ (D + 1))) + |C|) ?_
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  have hP0 : 0 ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := powLog_nonneg D n
  have hCP : C * (n : ℝ) ^ D * Real.log (n + 1) ≤ |C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self C) hP0
  have hCP' : -(|C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) ≤ C * (n : ℝ) ^ D * Real.log (n + 1) := by
    rw [mul_assoc, ← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_abs_le C) hP0
  have h2 : (1 : ℝ) ≤ 2 ^ (D + 1) := one_le_pow₀ (by norm_num)

  have hup : chiP D (n + k) - chiP D n ≤ k * (|C'| * 2 ^ (D + 1)) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
    refine (chiP_add_sub_le D C' hC' k n (by omega)).trans ?_
    calc ∑ j ∈ Finset.range k, |C'| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1))
        ≤ ∑ j ∈ Finset.range k, |C'| * (2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) := by
          refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (abs_nonneg C')
          exact powLog_shift_le D (by have := Finset.mem_range.1 hj; omega)
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

  have hdn : chiP D n - chiP D (n - k) ≤ k * (|C'| * 2 ^ (D + 1)) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
    have h := chiP_add_sub_le D C' hC' k (n - k) (by omega)
    rw [Nat.sub_add_cancel (by omega : k ≤ n)] at h
    refine h.trans ?_
    calc ∑ j ∈ Finset.range k, |C'| * (((n - k + j : ℕ) : ℝ) ^ D * Real.log (((n - k + j : ℕ) : ℝ) + 1))
        ≤ ∑ j ∈ Finset.range k, |C'| * (2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) := by
          refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (abs_nonneg C')
          have hj' := Finset.mem_range.1 hj
          refine (powLog_mono D (show n - k + j ≤ n by omega)).trans ?_
          exact le_mul_of_one_le_left hP0 h2
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hlo' := hlo n hn
  have hhi' := hhi n hn
  have hu := mul_le_mul_of_nonneg_left hup hδ
  have hd := mul_le_mul_of_nonneg_left hdn hδ
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hP0, abs_le]
  constructor
  · nlinarith
  · nlinarith

theorem defect_pullFS (hPB : ProjectionBounds.Statement) (hTop : TopPullFS.Statement) {D : ℕ} {Ω : Type}
    [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (I : AllFam) (hI : I.IsFamily) (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ) (hfr : IsProjFrame d.x e) (hFS : IsPullFS d.x e d.m) :
    (fun n => hsDefect D (resChi d) (top I d.x d.m D) n -
        (projDeg d.x e : ℝ) * hsDefect D (chiP D) (hhOf I D) n)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  obtain ⟨k, E, C, -, -, -, -, -, -, -, hs⟩ := hPB D Ω κ d e hfr hFS
  have ht := hTop D Ω κ I d.x d.m e hI d.arith d.smooth hfr hFS
  refine (sub_chiP_isBigO D k (projDeg d.x e) C (Nat.cast_nonneg _) (resChi d) (fun n hn => (hs n hn).1)
    (fun n hn => (hs n hn).2)).congr_left fun n => ?_
  simp only [hsDefect, ht]
  ring

theorem isLittleO_pow_pw (D : ℕ) : (fun n : ℕ => (n : ℝ) ^ D) =o[atTop] pw D :=
  (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (Nat.lt_succ_self D)).comp_tendsto tendsto_natCast_atTop_atTop

theorem proof (hPB : ProjectionBounds.Statement) (hCL : ChangeOfLattice.Statement)
    (hTop : TopPullFS.Statement) (hDeg : ProjDegGenDeg.Statement) (hInv : GenDegMatAct.Statement)
    (hFC : FrameChange.Statement) (hMF : MetricToFS.Statement) : ReductionToProjective.Statement := by
  intro D Ω _ _ κ _ I d hI
  refine ⟨fun e hfr hFS => defect_pullFS hPB hTop I hI d e hfr hFS, ?_⟩
  obtain ⟨B, d', e, hB, hx', hm', hfr', hidx⟩ := hFC D Ω κ d
  obtain ⟨d₀, hx₀, hFS₀, hmet⟩ := hMF D Ω κ I d' e hI hfr'
  have hfr₀ : IsProjFrame d₀.x e := hx₀ ▸ hfr'
  have hFS₀' : IsPullFS d₀.x e d₀.m := hx₀ ▸ hFS₀
  have h1 := (defect_pullFS hPB hTop I hI d₀ e hfr₀ hFS₀').trans_isLittleO (isLittleO_pow_mul_log D)
  rw [hx₀] at h1
  have h2 := (hCL D Ω κ I d.x B d.m d'.m hI d.arith d.indep hB d.smooth hm').trans_isLittleO
    (isLittleO_pow_pw D)
  rw [← hx'] at h2
  have hg : (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) = (projDeg d'.x e : ℝ) := by
    have hd := hDeg D Ω κ d'.x e d'.arith hfr'
    have hi := hInv D Ω κ d.x B hB
    rw [← hx', hd] at hi
    rw [← hi]
    push_cast
    rfl
  rw [hg]
  refine ((h1.sub hmet).sub (hidx.add h2)).congr_left fun n => ?_
  simp only [hsDefect]
  ring

end ReductionToProjective

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTopConstantTwist
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

set_option linter.unusedSectionVars false

namespace TopConstantTwistAlt

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

theorem cxHessian_add_const (f : (Fin e → ℂ) → ℝ) (C : ℝ) (y : Fin e → ℂ) :
    cxHessian (fun y' => f y' + C) y = cxHessian f y := by
  have h : fderiv ℝ (fun y' => f y' + C) = fderiv ℝ f := funext fun _ => fderiv_add_const _
  unfold cxHessian
  rw [h]

theorem ptsIntegral_congr_add_const (P : Ideal (MRing ι)) (φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (C : Fin e → ℝ) (h : ∀ j z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → φ j z = φ' j z + C j)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : ptsIntegral P φ g = ptsIntegral P φ' g := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    congr 1
    funext y
    refine finsum_congr fun w => finsum_congr fun _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · congr 1
      unfold maDensity
      congr 3
      funext j
      have hev : (fun y' => φ j (hγ.choose y')) =ᶠ[𝓝 y] (fun y' => φ' j (hγ.choose y') + C j) := by
        filter_upwards [hγ.choose_spec.2] with y' hy'
        exact h j _ hy'.2.1.1
      rw [cxHessian_congr hev, cxHessian_add_const]
    · rfl
  · rfl

theorem ptsIntegral_const_weight (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun _ => c) = c * ptsIntegral P φ (fun _ => 1) := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
    refine finsum_congr fun w => ?_
    congr 1
    funext _
    unfold sheetDensity
    split_ifs <;> ring
  · ring

theorem ptsIntegral_twist_term (P : Ideal (MRing ι)) (A : HermLine ι) (c : ℝ) (D i : ℕ) :
    ptsIntegral P (pot fun j : Fin D => if (j : ℕ) < i then A.tensor (constLine c) else A) (fun _ => c) =
      c * geomDeg P A D := by
  rw [ptsIntegral_const_weight, geomDeg]
  congr 1
  refine ptsIntegral_congr_add_const P _ _ (fun j => if (j : ℕ) < i then -c else 0) (fun j z hz => ?_) _
  unfold pot
  dsimp only
  split_ifs
  · show Real.log (A.h z * Real.exp (-c)) = Real.log (A.h z) + -c
    rw [Real.log_mul (A.pos z hz).ne' (Real.exp_pos _).ne', Real.log_exp]
  · simp

end TopConstantTwistAlt


open TopConstantTwistAlt in
theorem TopConstantTwist.proof : TopConstantTwist.Statement := by
  intro K _ ι _ P D A c II hII hP hA
  have h : II K ι P (D + 1) (fun _ => A.tensor (constLine c)) - II K ι P (D + 1) (fun _ => A) =
      -∑ i ∈ Finset.range (D + 1),
        ptsIntegral P (pot fun j : Fin D => if (j : ℕ) < i then A.tensor (constLine c) else A) (fun _ => c) :=
    GroundTheory.Heights₂.Heights.Telescope.proof K ι (II K ι) (hII K ι) P D A (fun _ => c) (fun _ _ _ => rfl) hP hA
      contDiffOn_const
  simp only [ptsIntegral_twist_term, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  push_cast at h ⊢
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResolutionMetricObjects
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory
open scoped ComplexConjugate

noncomputable section

set_option linter.unusedSectionVars false

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def resCGram (d : HSMDatum D Ω κ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Ix κ) ℚ) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun k l => ∫ y, pairVal d.m n (b k) (b l) (resPt d y) ∂d.dV


open Classical in
def resCChi (d : HSMDatum D Ω κ) (n : ℕ) : ℝ :=
  if h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2 then
    -(1 / 2) * Real.log (resCGram d n h.choose.2).det.re
  else 0

def resPot (d : HSMDatum D Ω κ) (m : ConeMetric ℂ (Ix κ)) : LocPot d.R.X where
  U := d.R.U
  isOpen_U := d.R.isOpen_U
  mem_U := d.R.mem_U
  φ x y := Real.log (m.ρ (d.R.lift x y))

def resMetricInt (d : HSMDatum D Ω κ) (m₁ : ConeMetric ℂ (Ix κ)) : ℝ :=
  ∫ t in (0 : ℝ)..1, mInt d.R.A (fun _ => resPot d (interp d.m m₁ t)) fun y => logRatio d.m m₁ (resPt d y)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

