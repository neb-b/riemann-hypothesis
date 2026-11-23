module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralRightCosetFunEqFinsum
section
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory

theorem integral_rightCoset_fun_eq_finsum (G Λ : Type) [Group G] [TopologicalSpace G] [ContinuousMul G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulRightInvariant] (H : Set G)
    (hH : IsOpen H) (hμ : μ H = 1) (π : G → Λ) (hπ : ∀ g g', π g' = π g ↔ g' * g⁻¹ ∈ H)
    (s : Λ → ℂ) (hs : ∀ l, s l = 0 ∨ ‖s l‖ = 1) :
    ∫ g, s (π g) ∂μ = ∑ᶠ l ∈ Set.range π, s l := by
  classical

  have hfib : ∀ g, π ⁻¹' {π g} = (fun x => x * g⁻¹) ⁻¹' H := by
    intro g; ext x; simp [hπ g x]
  have hfibO : ∀ g, IsOpen (π ⁻¹' {π g}) := by
    intro g; rw [hfib g]; exact hH.preimage (continuous_mul_const _)
  have hfibM : ∀ l, MeasurableSet (π ⁻¹' {l}) := by
    intro l
    by_cases hl : l ∈ Set.range π
    · obtain ⟨g, rfl⟩ := hl; exact (hfibO g).measurableSet
    · have : π ⁻¹' {l} = ∅ := by
        ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun h => hl ⟨x, h⟩
      rw [this]; exact MeasurableSet.empty
  have hfib1 : ∀ g, μ (π ⁻¹' {π g}) = 1 := by
    intro g; rw [hfib g, measure_preimage_mul_right, hμ]
  set S := Set.range π ∩ Function.support s with hSdef
  by_cases hS : S.Finite
  · set T := hS.toFinset with hT
    have hfun : (fun g => s (π g)) = fun g => ∑ l ∈ T, (π ⁻¹' {l}).indicator (fun _ => s l) g := by
      funext g
      have : ∀ l, (π ⁻¹' {l}).indicator (fun _ => s l) g = if π g = l then s (π g) else 0 := by
        intro l
        by_cases h : π g = l
        · subst h; simp
        · simp [Set.indicator_apply, h]
      simp only [this, Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · have : π g ∉ S := by rw [hT, Set.Finite.mem_toFinset] at *; exact h
        by_contra hne
        exact this ⟨⟨g, rfl⟩, Ne.symm hne |>.symm⟩
    rw [hfun, MeasureTheory.integral_finsetSum]
    · rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hS]
      refine Finset.sum_congr rfl ?_
      intro l hl
      rw [integral_indicator_const _ (hfibM l)]
      have hl' : l ∈ Set.range π := ((Set.Finite.mem_toFinset hS).1 hl).1
      obtain ⟨g, rfl⟩ := hl'
      simp [Measure.real, hfib1 g]
    · intro l _
      exact (integrable_indicator_iff (hfibM l)).2 (by
        by_cases hl : l ∈ Set.range π
        · obtain ⟨g, rfl⟩ := hl
          haveI : IsFiniteMeasure (μ.restrict (π ⁻¹' {π g})) := ⟨by simp [hfib1 g]⟩
          exact integrable_const _
        · have : π ⁻¹' {l} = ∅ := by
            ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
            exact fun h => hl ⟨x, h⟩
          rw [this]; exact integrableOn_empty)
  · rw [finsum_mem_eq_zero_of_infinite hS]
    apply integral_undef
    intro hint
    have hfin := hint.2

    have hbound : ∀ F : Finset Λ, (↑F : Set Λ) ⊆ S → (F.card : ENNReal) ≤ ∫⁻ g, ‖s (π g)‖ₑ ∂μ := by
      intro F hF
      calc (F.card : ENNReal) = ∑ l ∈ F, μ (π ⁻¹' {l}) := by
            rw [Finset.card_eq_sum_ones, Nat.cast_sum]
            refine Finset.sum_congr rfl ?_
            intro l hl
            obtain ⟨⟨g, rfl⟩, _⟩ := hF hl
            simp [hfib1 g]
        _ = ∫⁻ g, ∑ l ∈ F, (π ⁻¹' {l}).indicator 1 g ∂μ := by
            rw [MeasureTheory.lintegral_finsetSum]
            · refine Finset.sum_congr rfl ?_
              intro l _
              rw [lintegral_indicator_one (hfibM l)]
            · intro l _
              exact (measurable_one.indicator (hfibM l))
        _ ≤ ∫⁻ g, ‖s (π g)‖ₑ ∂μ := by
            apply lintegral_mono
            intro g
            have : ∀ l, (π ⁻¹' {l}).indicator (1 : G → ENNReal) g = if π g = l then 1 else 0 := by
              intro l; simp [Set.indicator_apply]
            simp only [this, Finset.sum_ite_eq]
            split_ifs with h
            · obtain ⟨_, hsupp⟩ := hF h
              rcases hs (π g) with h0 | h1
              · exact absurd h0 hsupp
              · rw [← ofReal_norm_eq_enorm, h1]; simp
            · exact bot_le
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfin.ne
    obtain ⟨F, hFS, hFc⟩ := Set.Infinite.exists_subset_card_eq (hS : S.Infinite) n
    have := hbound F hFS
    rw [hFc] at this
    exact absurd (lt_of_le_of_lt this hn) (lt_irrefl _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCompactFiniteEtaleHermitianPairOK
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.OKCompact

theorem continuous_coeff_charpoly {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {n : ℕ}
    (k : ℕ) : Continuous fun M : Matrix (Fin n) (Fin n) A => M.charpoly.coeff k := by
  have : (fun M : Matrix (Fin n) (Fin n) A => M.charpoly.coeff k) = fun M =>
      MvPolynomial.eval (fun p : Fin n × Fin n => M p.1 p.2)
        (MvPolynomial.map (Int.castRingHom A) ((Matrix.charpoly.univ ℤ (Fin n)).coeff k)) := by
    funext M
    rw [MvPolynomial.eval_map]
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (Int.castRingHom A) (fun p => M p.1 p.2) k).symm
  rw [this]
  exact (MvPolynomial.continuous_eval _).comp (by fun_prop)

theorem charpoly_smul_eq_scaleRoots {K : Type} [Field K] [Infinite K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    {c : K} (hc : c ≠ 0) : (c • M).charpoly = M.charpoly.scaleRoots c := by
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [Polynomial.scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

variable {F : Type} [NontriviallyNormedField F] {K : Type} [CommRing K] [Algebra F K] [Module.Finite F K]

theorem coeff_charpoly_lmul_smul [Infinite F] (z : K) {c : F} (hc : c ≠ 0) (k : ℕ) :
    (LinearMap.charpoly (Algebra.lmul F K (c • z))).coeff k =
      (LinearMap.charpoly (Algebra.lmul F K z)).coeff k * c ^ (Module.finrank F K - k) := by
  let b := Module.finBasis F K
  rw [← LinearMap.charpoly_toMatrix (Algebra.lmul F K (c • z)) b,
    ← LinearMap.charpoly_toMatrix (Algebra.lmul F K z) b, map_smul, map_smul,
    charpoly_smul_eq_scaleRoots _ hc, Polynomial.coeff_scaleRoots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem continuous_coeff_lmul [TopologicalSpace K] [IsModuleTopology F K] (k : ℕ) :
    Continuous fun z : K => (LinearMap.charpoly (Algebra.lmul F K z)).coeff k := by
  let b := Module.finBasis F K
  have h : (fun z : K => (LinearMap.charpoly (Algebra.lmul F K z)).coeff k) =
      (fun M : Matrix _ _ F => M.charpoly.coeff k) ∘ (fun z => Algebra.leftMulMatrix b z) := by
    funext z
    simp only [Function.comp, Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
  rw [h]
  refine (continuous_coeff_charpoly k).comp ?_
  refine continuous_matrix fun i j => ?_
  let l : K →ₗ[F] F :=
    { toFun := fun z => Algebra.leftMulMatrix b z i j
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  exact IsModuleTopology.continuous_of_linearMap l

end GlobalTheory.JR.OKCompact

namespace GlobalTheory.JR.OKCompact

theorem okCompact : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E), IsCompact A.OK := by
  intro F E _ _ _ _ hU A
  haveI : CharZero F := hU.charZero
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank F A.K = n := ⟨_, rfl⟩
  let e : A.K ≃ₗ[F] (Fin n → F) := (Module.finBasisOfFinrankEq F A.K hn).equivFun
  have hes : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let P : ℕ → A.K → F := fun k z => (LinearMap.charpoly (Algebra.lmul F A.K z)).coeff k
  have hPc : ∀ k, Continuous (P k) := fun k => continuous_coeff_lmul k
  have hcl : IsClosed A.OK := by
    have : A.OK = ⋂ k, {z | ‖P k z‖ ≤ 1} := by ext z; simp [Et.OK, P]
    rw [this]
    exact isClosed_iInter fun k => isClosed_le (continuous_norm.comp (hPc k)) continuous_const
  have hzero : ∀ z : A.K, (∀ k < n, P k z = 0) → z = 0 := by
    intro z hz
    have hp : LinearMap.charpoly (Algebra.lmul F A.K z) = Polynomial.X ^ n := by
      ext k
      rw [Polynomial.coeff_X_pow]
      rcases lt_trichotomy k n with hk | hk | hk
      · rw [if_neg hk.ne]; exact hz k hk
      · rw [if_pos hk]
        have := (LinearMap.charpoly_monic (Algebra.lmul F A.K z)).coeff_natDegree
        rwa [LinearMap.charpoly_natDegree, hn, ← hk] at this
      · rw [if_neg hk.ne']
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [LinearMap.charpoly_natDegree, hn]; exact hk
    have hCH := LinearMap.aeval_self_charpoly (Algebra.lmul F A.K z)
    rw [hp, map_pow, Polynomial.aeval_X, ← map_pow] at hCH
    have h1 := LinearMap.congr_fun hCH 1
    have h2 : z ^ n = 0 := by simpa using h1
    exact IsReduced.eq_zero z ⟨n, h2⟩
  obtain ⟨a, ha⟩ := NormedField.exists_one_lt_norm F
  let T : Set (Fin n → F) := {v | 1 ≤ ‖v‖ ∧ ‖v‖ ≤ ‖a‖}
  have hT : IsCompact T := (isCompact_closedBall (0 : Fin n → F) ‖a‖).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
      (fun v hv => mem_closedBall_zero_iff.2 hv.2)
  let h : (Fin n → F) → ℝ := fun v => ∑ k ∈ Finset.range n, ‖P k (e.symm v)‖
  have hc : Continuous h := continuous_finsetSum _ fun k _ => continuous_norm.comp ((hPc k).comp hes)
  have hpos : ∀ v ∈ T, 0 < h v := by
    intro v hv
    by_contra hle
    push_neg at hle
    have hsum : h v = 0 := le_antisymm hle (Finset.sum_nonneg fun k _ => norm_nonneg _)
    have h0 : ∀ k < n, P k (e.symm v) = 0 := by
      intro k hk
      exact norm_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun k _ => norm_nonneg (P k (e.symm v))).1 hsum k
        (Finset.mem_range.2 hk))
    have hv0 : v = 0 := by simpa using congrArg e (hzero _ h0)
    have := hv.1
    rw [hv0, norm_zero] at this
    linarith
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ v ∈ T, m ≤ h v := by
    rcases T.eq_empty_or_nonempty with hTe | hTn
    · exact ⟨1, one_pos, fun v hv => by rw [hTe] at hv; exact hv.elim⟩
    · obtain ⟨v₀, hv₀, hmin⟩ := hT.exists_isMinOn hTn hc.continuousOn
      exact ⟨h v₀, hpos v₀ hv₀, fun v hv => hmin hv⟩
  have hsub : A.OK ⊆ e.symm '' Metric.closedBall 0 (‖a‖ * max 1 (n / m)) := by
    intro z hz
    refine ⟨e z, ?_, e.symm_apply_apply z⟩
    rw [mem_closedBall_zero_iff]
    have hR : ‖a‖ ≤ ‖a‖ * max 1 (n / m) := le_mul_of_one_le_right (norm_nonneg _) (le_max_left _ _)
    by_cases hv : e z = 0
    · rw [hv, norm_zero]; linarith
    obtain ⟨d, hd0, hd1, hd2, -⟩ := rescale_to_shell ha (by linarith : (0 : ℝ) < ‖a‖) hv
    have hwT : d • e z ∈ T := ⟨by rwa [div_self (by linarith : ‖a‖ ≠ 0)] at hd2, hd1.le⟩
    have hvw : e z = d⁻¹ • (d • e z) := by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
    have hnv : ‖e z‖ = ‖d⁻¹‖ * ‖d • e z‖ := by rw [← norm_smul, ← hvw]
    have hsc : ∀ k, P k (e.symm (e z)) = P k (e.symm (d • e z)) * d⁻¹ ^ (n - k) := by
      intro k
      conv_lhs => rw [hvw, map_smul]
      have := coeff_charpoly_lmul_smul (F := F) (e.symm (d • e z)) (inv_ne_zero hd0) k
      rw [hn] at this
      exact this
    have hhv : h (e z) ≤ n := by
      calc h (e z) ≤ ∑ k ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
              show ‖P k (e.symm (e z))‖ ≤ 1
              rw [e.symm_apply_apply]; exact hz k
        _ = n := by simp
    by_cases hc1 : ‖d⁻¹‖ ≤ 1
    · calc ‖e z‖ = ‖d⁻¹‖ * ‖d • e z‖ := hnv
        _ ≤ 1 * ‖a‖ := mul_le_mul hc1 hwT.2 (norm_nonneg _) zero_le_one
        _ ≤ _ := by rw [one_mul]; exact hR
    · push_neg at hc1
      have hlow : ‖d⁻¹‖ * m ≤ h (e z) := by
        calc ‖d⁻¹‖ * m ≤ ‖d⁻¹‖ * h (d • e z) := mul_le_mul_of_nonneg_left (hm _ hwT) (norm_nonneg _)
          _ = ∑ k ∈ Finset.range n, ‖d⁻¹‖ * ‖P k (e.symm (d • e z))‖ := Finset.mul_sum _ _ _
          _ ≤ ∑ k ∈ Finset.range n, ‖P k (e.symm (e z))‖ := Finset.sum_le_sum fun k hk => by
              rw [hsc k, norm_mul, norm_pow, mul_comm]
              apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
              have hk' : 1 ≤ n - k := by have := Finset.mem_range.1 hk; omega
              calc ‖d⁻¹‖ = ‖d⁻¹‖ ^ 1 := (pow_one _).symm
                _ ≤ ‖d⁻¹‖ ^ (n - k) := pow_le_pow_right₀ hc1.le hk'
      have hcm : ‖d⁻¹‖ ≤ n / m := by rw [le_div_iff₀ hm0]; linarith
      calc ‖e z‖ = ‖d⁻¹‖ * ‖d • e z‖ := hnv
        _ ≤ (n / m) * ‖a‖ := mul_le_mul hcm hwT.2 (norm_nonneg _) (by positivity)
        _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)
  exact ((isCompact_closedBall 0 _).image hes).of_isClosed_subset hcl hsub

end GlobalTheory.JR.OKCompact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCompactPreimageMulStarAnisotropicSubmodule
section
open GlobalTheory.JR Matrix

namespace GlobalTheory

theorem mul_star_anisotropic_proper : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (V : Submodule E (Matrix (Fin r) (Fin r) E)), (∀ z ∈ V, z * star z = 0 → z = 0) → ∀ B : Set (Matrix (Fin r) (Fin r) E), IsCompact B → IsCompact {z : Matrix (Fin r) (Fin r) E | z ∈ V ∧ z * star z ∈ B} := by
  intro F E _ _ _ _ hU r V hV B hB
  letI : NormedAddCommGroup (Matrix (Fin r) (Fin r) E) := Matrix.normedAddCommGroup
  letI : NormedSpace E (Matrix (Fin r) (Fin r) E) := Matrix.normedSpace
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : ProperSpace (Matrix (Fin r) (Fin r) E) := FiniteDimensional.proper E _
  have hsE : Continuous (star : E → E) :=
    AddMonoidHomClass.continuous_of_bound (starAddEquiv : E ≃+ E) 1 (fun x => by simp [hU.norm_star])
  haveI : ContinuousStar E := ⟨hsE⟩
  have hQc : Continuous fun z : Matrix (Fin r) (Fin r) E => z * star z :=
    continuous_id.mul continuous_star
  have hQs : ∀ (d : E) (z : Matrix (Fin r) (Fin r) E), (d • z) * star (d • z) = (d * star d) • (z * star z) := by
    intro d z
    rw [star_smul, smul_mul_smul_comm]
  have hnd : ∀ d : E, ‖d * star d‖ = ‖d‖ ^ 2 := by
    intro d; rw [norm_mul, hU.norm_star, sq]
  have hVc : IsClosed (V : Set (Matrix (Fin r) (Fin r) E)) := Submodule.closed_of_finiteDimensional V
  obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm E
  set A : Set (Matrix (Fin r) (Fin r) E) := {w | w ∈ V ∧ ‖k‖⁻¹ ≤ ‖w‖ ∧ ‖w‖ ≤ 1} with hA
  have hAc : IsCompact A := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact hVc.inter ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    · exact (Metric.isBounded_closedBall (x := (0 : Matrix (Fin r) (Fin r) E)) (r := 1)).subset
        (fun w hw => by simpa using hw.2.2)
  have hkpos : 0 < ‖k‖⁻¹ := inv_pos.mpr (lt_trans one_pos hk)
  have hA0 : ∀ w ∈ A, 0 < ‖w * star w‖ := by
    intro w hw
    apply norm_pos_iff.mpr
    intro h0
    have := hV w hw.1 h0
    have h1 := hw.2.1
    rw [this, norm_zero] at h1
    linarith
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ w ∈ A, c ≤ ‖w * star w‖ := by
    rcases A.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨w₀, hw₀, hmin⟩ := hAc.exists_isMinOn hne (hQc.norm.continuousOn)
      exact ⟨_, hA0 w₀ hw₀, fun w hw => hmin hw⟩
  obtain ⟨R, hR⟩ := (hB.isBounded).subset_closedBall 0
  apply Metric.isCompact_of_isClosed_isBounded
  · exact hVc.inter (hB.isClosed.preimage hQc)
  · apply (Metric.isBounded_closedBall (x := (0 : Matrix (Fin r) (Fin r) E)) (r := Real.sqrt (|R| / c))).subset
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hQR : ‖z * star z‖ ≤ |R| := by
      have := hR hz.2
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_abs_self R)
    by_cases hz0 : z = 0
    · rw [hz0, norm_zero]; exact Real.sqrt_nonneg _
    obtain ⟨d, hd0, hd1, hd2, -⟩ := rescale_to_shell hk one_pos hz0
    have hdA : d • z ∈ A := ⟨V.smul_mem d hz.1, by simpa using hd2, hd1.le⟩
    have h1 := hc _ hdA
    rw [hQs, norm_smul, hnd] at h1
    rw [norm_smul] at hd1
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hc0]
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd0

    have hdz : (‖d‖ * ‖z‖) ^ 2 ≤ 1 := by
      have : 0 ≤ ‖d‖ * ‖z‖ := by positivity
      nlinarith
    have hQ0 : 0 ≤ ‖z * star z‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖z‖)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFullLatticeProdOfComapInlMapSnd
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem isLat_of_comap_inl_of_map_snd (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A))
    (h₁ : IsLat K.O K.E (M.comap (LinearMap.inl K.O B₁.A B₂.A)))
    (h₂ : IsLat K.O K.E (M.map (LinearMap.snd K.O B₁.A B₂.A))) : IsLat K.O K.E M := by
  obtain ⟨f₁, s₁⟩ := h₁
  obtain ⟨f₂, s₂⟩ := h₂
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd K.O B₁.A B₂.A) f₂ ?_
    have : M ⊓ LinearMap.ker (LinearMap.snd K.O B₁.A B₂.A) =
        (M.comap (LinearMap.inl K.O B₁.A B₂.A)).map (LinearMap.inl K.O B₁.A B₂.A) := by
      ext ⟨a, b⟩
      simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.snd_apply, Submodule.mem_map,
        Submodule.mem_comap, LinearMap.inl_apply]
      constructor
      · rintro ⟨hM, rfl⟩
        exact ⟨a, hM, rfl⟩
      · rintro ⟨c, hc, he⟩
        rw [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨hc, rfl⟩
    rw [this]
    exact f₁.map _
  · set S := Submodule.span K.E (M : Set (B₁.A × B₂.A)) with hS
    have hinl : ∀ a : B₁.A, ((a, 0) : B₁.A × B₂.A) ∈ S := by
      intro a
      have ha : a ∈ Submodule.span K.E ((M.comap (LinearMap.inl K.O B₁.A B₂.A) : Submodule K.O B₁.A) : Set B₁.A) := by
        rw [s₁]; trivial
      have hle : (Submodule.span K.E ((M.comap (LinearMap.inl K.O B₁.A B₂.A) : Submodule K.O B₁.A) : Set B₁.A)).map
          (LinearMap.inl K.E B₁.A B₂.A) ≤ S := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨c, hc, rfl⟩
        exact hc
      exact hle ⟨a, ha, rfl⟩
    have hsnd : S.map (LinearMap.snd K.E B₁.A B₂.A) = ⊤ := by
      rw [hS, Submodule.map_span, ← s₂]
      congr 1
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have hb : b ∈ S.map (LinearMap.snd K.E B₁.A B₂.A) := by rw [hsnd]; trivial
    obtain ⟨y, hy, hyb⟩ := hb
    have : ((a, b) : B₁.A × B₂.A) = y + (a - y.1, 0) := by
      ext
      · simp
      · simp [← hyb]
    rw [this]
    exact S.add_mem hy (hinl _)

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralIffForallMaximalSpectrumResidue
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem isIntegral_iff_forall_maximalSpectrum (K : UQ) (B : InvAlg K) (hred : IsReduced B.A) (x : B.A) :
    IsIntegral K.O x ↔ ∀ m : MaximalSpectrum B.A, IsIntegral K.O (Ideal.Quotient.mk m.asIdeal x) := by
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  constructor
  · intro h m
    have := h.map (Ideal.Quotient.mkₐ K.O m.asIdeal)
    simpa [Ideal.Quotient.mkₐ_eq_mk] using this
  · intro h
    letI : Fintype (MaximalSpectrum B.A) := Fintype.ofFinite _
    choose p hpm hp using fun m : MaximalSpectrum B.A => h m
    refine ⟨∏ m, p m, monic_prod_of_monic _ _ (fun m _ => hpm m), ?_⟩
    have hmem : ∀ m : MaximalSpectrum B.A, eval₂ (algebraMap K.O B.A) x (∏ m, p m) ∈ m.asIdeal := by
      intro m
      rw [Polynomial.eval₂_finsetProd]
      classical
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
      apply Ideal.mul_mem_right
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have h1 := hp m
      have h2 := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ K.O m.asIdeal) x (p m)
      rw [Ideal.Quotient.mkₐ_eq_mk, aeval_def, h1] at h2
      rw [← aeval_def]
      exact h2.symm
    set z := eval₂ (algebraMap K.O B.A) x (∏ m, p m)
    have hj : z ∈ Ideal.jacobson (⊥ : Ideal B.A) := by
      rw [Ideal.jacobson, Submodule.mem_sInf]
      rintro J ⟨-, hJ⟩
      exact hmem ⟨J, hJ⟩
    obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B.A)
    have hz : z ^ k = 0 := by
      have := Ideal.pow_mem_pow hj k
      rw [hk] at this
      simpa using this
    exact IsReduced.eq_zero z ⟨k, hz⟩

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitting
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def WeilAt (A : Et F E) : Prop :=
  ∀ ψ : AddChar F ℂ, IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L), SelfDual μ (A.kerL ψ x) →
    ∃ γ W, A.IsWeil ψ x A.etaK μ γ W

def IsSplitting (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L) : Prop :=
  (∀ k : A.K, eL (algebraMap A.K A.L k) = (algebraMap A₁.K A₁.L (eK k).1, algebraMap A₂.K A₂.L (eK k).2)) ∧
  (∀ e : E, eL (algebraMap E A.L e) = (algebraMap E A₁.L e, algebraMap E A₂.L e)) ∧
  ∀ y : A.L, eL (star y) = (star (eL y).1, star (eL y).2)

end GlobalTheory.JR
end
end

