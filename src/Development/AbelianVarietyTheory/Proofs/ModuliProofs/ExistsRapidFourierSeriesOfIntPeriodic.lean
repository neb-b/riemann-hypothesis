module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LatticeFourierOfContDiffFiniteDimensional

@[expose] public section

open Complex Matrix
open scoped ContDiff BigOperators Real RealInnerProductSpace

namespace GlobalTheory

private theorem mem_intLattice_iff {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) ↔
      ∃ ν : Fin n → ℤ, x = WithLp.toLp 2 fun k => (ν k : ℝ) := by
  rw [Module.Basis.mem_span_iff_repr_mem]
  constructor
  · intro h
    choose ν hν using h
    refine ⟨ν, ?_⟩
    ext k
    simpa using (hν k).symm
  · rintro ⟨ν, rfl⟩ i
    exact ⟨ν i, by simp⟩

private theorem mem_intLattice_dual_iff {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin n)))
      (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)) ↔
      ∃ ν : Fin n → ℤ, x = WithLp.toLp 2 fun k => (ν k : ℝ) := by
  simp only [LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one, innerₗ_apply_apply]
  constructor
  · intro h
    choose m hm using fun k => h ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis k)
      (Submodule.subset_span ⟨k, rfl⟩)
    refine ⟨m, ?_⟩
    ext k
    simpa [EuclideanSpace.inner_single_right] using (hm k).symm
  · rintro ⟨ν, rfl⟩ y hy
    obtain ⟨μ, rfl⟩ := (mem_intLattice_iff y).1 hy
    exact ⟨∑ k, μ k * ν k, by simp [PiLp.inner_apply]⟩

theorem exists_rapid_fourierSeries_of_int_periodic :
    ∀ (n : ℕ) (w : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ w →
      (∀ (ν : Fin n → ℤ) x, w (x + fun k => (ν k : ℝ)) = w x) →
      ∃ c : (Fin n → ℤ) → ℂ, (∀ N : ℕ, ∃ C : ℝ, ∀ ν, ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N ≤ C) ∧
        ∀ x, w x = ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) := by
  intro n w hw hper
  classical
  let L : Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
    Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
  let A : EuclideanSpace ℝ (Fin n) → ℂ := fun y => w y.ofLp
  have hA : ContDiff ℝ ∞ A := hw.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff
  have hAp : ∀ x ∈ L, Function.Periodic A x := fun x hx y => by
    obtain ⟨ν, rfl⟩ := (mem_intLattice_iff x).1 hx
    exact hper ν y.ofLp
  let v : (Fin n → ℤ) → EuclideanSpace ℝ (Fin n) := fun ν => WithLp.toLp 2 fun k => (ν k : ℝ)
  let φ : (Fin n → ℤ) ≃ L :=
    Equiv.ofBijective (fun ν => ⟨v ν, (mem_intLattice_iff _).2 ⟨ν, rfl⟩⟩) ⟨fun ν μ h => by
      funext k
      have := congrArg (fun z : L => (z.1 : EuclideanSpace ℝ (Fin n)).ofLp k) h
      simpa [v] using this, fun z => by
      obtain ⟨ν, hν⟩ := (mem_intLattice_iff z.1).1 z.2
      exact ⟨ν, Subtype.ext hν.symm⟩⟩
  let p : (Fin n → ℝ) → UnitAddTorus (Fin n) := fun x i => (x i : UnitAddCircle)
  have hp : IsOpenQuotientMap p :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  let q : EuclideanSpace ℝ (Fin n) → UnitAddTorus (Fin n) := fun y => p y.ofLp
  have hq : Function.Surjective q := fun t => by
    obtain ⟨x, hx⟩ := hp.surjective t
    exact ⟨WithLp.toLp 2 x, hx⟩
  have hqadd (x y : EuclideanSpace ℝ (Fin n)) : q (x + y) = q x + q y := by
    funext i
    exact AddCircle.coe_add (p := (1 : ℝ)) (x.ofLp i) (y.ofLp i)
  -- Periodicity lets the function descend to the torus.
  let F : UnitAddTorus (Fin n) → ℂ := fun t => w (Function.surjInv hp.surjective t)
  have hFp (x : Fin n → ℝ) : F (p x) = w x := by
    let y := Function.surjInv hp.surjective (p x)
    have hy : p y = p x := Function.surjInv_eq _ _
    have hi (i : Fin n) : ((y i - x i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, sub_eq_zero]
      exact congrFun hy i
    choose ν hν using fun i => (AddCircle.coe_eq_zero_iff _).1 (hi i)
    have hyx : y = x + fun i => (ν i : ℝ) := by
      funext i
      have h := hν i
      simp only [zsmul_eq_mul, mul_one] at h
      change y i = x i + (ν i : ℝ)
      linarith
    exact (congrArg w hyx).trans (hper ν x)
  have hF : Continuous F :=
    hp.isQuotientMap.continuous_iff.2 (by
      rw [show F ∘ p = w from funext hFp]
      exact hw.continuous)
  let f : C(UnitAddTorus (Fin n), ℂ) := ⟨F, hF⟩
  have hchar (ν : Fin n → ℤ) (x : Fin n → ℝ) :
      UnitAddTorus.mFourier ν (p x) =
        cexp (2 * π * I * ∑ i, (ν i : ℂ) * (x i : ℂ)) := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, p, fourier_coe_apply,
      ofReal_one, div_one, ← Complex.exp_sum, Finset.mul_sum, mul_assoc]
  have hcharE (ν : Fin n → ℤ) (y : EuclideanSpace ℝ (Fin n)) :
      UnitAddTorus.mFourier ν (q y) = cexp (2 * π * I * ((⟪v ν, y⟫ : ℝ) : ℂ)) := by
    rw [show q y = p y.ofLp from rfl, hchar]
    simp [v, PiLp.inner_apply, mul_comm]
  let : MeasureTheory.MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  let : (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle).IsAddHaarMeasure :=
    inferInstanceAs (AddCircle.haarAddCircle : MeasureTheory.Measure UnitAddCircle).IsAddHaarMeasure
  let : MeasureTheory.IsProbabilityMeasure (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
    inferInstanceAs (MeasureTheory.IsProbabilityMeasure
      (AddCircle.haarAddCircle : MeasureTheory.Measure UnitAddCircle))
  have hnorm (ν : Fin n → ℤ) (t : UnitAddTorus (Fin n)) :
      ‖UnitAddTorus.mFourier ν t‖ = 1 := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply,
      Circle.norm_coe, Finset.prod_const_one]
  have hcoeffBound (g : UnitAddTorus (Fin n) → ℂ) (ν : Fin n → ℤ) (B : ℝ)
      (hB : ∀ t, ‖g t‖ ≤ B) : ‖UnitAddTorus.mFourierCoeff g ν‖ ≤ B := by
    unfold UnitAddTorus.mFourierCoeff
    simpa only [MeasureTheory.probReal_univ, mul_one] using
      (MeasureTheory.norm_integral_le_of_norm_le_const
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin n))))
        (Filter.Eventually.of_forall fun t => by
          rw [norm_smul, hnorm, one_mul]
          exact hB t))
  have hdiff (ν : Fin n → ℤ) (u : UnitAddTorus (Fin n))
      (hu : ∀ t, UnitAddTorus.mFourier (-ν) (t + u) = -UnitAddTorus.mFourier (-ν) t)
      (k : ℕ) (g : UnitAddTorus (Fin n) → ℂ) (hg : Continuous g) :
      UnitAddTorus.mFourierCoeff ((fwdDiff u)^[k] g) ν =
        (-2 : ℂ) ^ k * UnitAddTorus.mFourierCoeff g ν := by
    induction k generalizing g with
    | zero => simp
    | succ k ih =>
      have hgu : Continuous (fun t : UnitAddTorus (Fin n) => g (t + u)) :=
        hg.comp (continuous_id.add continuous_const)
      have hc : Continuous (fwdDiff u g) := hgu.sub hg
      rw [Function.iterate_succ_apply, ih _ hc, pow_succ, mul_assoc]
      congr 1
      unfold UnitAddTorus.mFourierCoeff
      simp only [fwdDiff, smul_sub]
      have hm := (UnitAddTorus.mFourier (-ν)).continuous
      rw [MeasureTheory.integral_sub]
      · have hshift := MeasureTheory.integral_add_right_eq_self
          (μ := (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin n))))
          (fun t => UnitAddTorus.mFourier (-ν) t • g t) u
        simp only [hu, neg_smul, MeasureTheory.integral_neg] at hshift
        linear_combination -hshift
      · exact (hm.smul hgu).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact (hm.smul hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpull (d : EuclideanSpace ℝ (Fin n)) (k : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
      (fwdDiff (q d))^[k] F (q y) = (fwdDiff d)^[k] A y := by
    induction k generalizing y with
    | zero => exact hFp y.ofLp
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp only [fwdDiff, ← hqadd, ih]
  let c : (Fin n → ℤ) → ℂ := UnitAddTorus.mFourierCoeff f
  have hbd : ∀ k : ℕ, ∃ M, ∀ ν, (4 * ‖v ν‖) ^ k * ‖c ν‖ ≤ M := by
    intro k
    have hAk : ContDiff ℝ k A := hA.of_le (by exact_mod_cast le_top)
    obtain ⟨M, hM⟩ := exists_bound_of_lattice_periodic (L := L) (f := iteratedFDeriv ℝ k A)
      (fun x hx b => by
        rw [← iteratedFDeriv_comp_add_right, show (fun z => A (z + x)) = A from funext (hAp x hx)])
      (hAk.continuous_iteratedFDeriv le_rfl)
    refine ⟨M, fun ν => ?_⟩
    rcases eq_or_ne (v ν) 0 with hzero | hzero
    · cases k with
      | zero =>
        simp only [pow_zero, one_mul]
        exact hcoeffBound F ν M fun t => by
          obtain ⟨y, rfl⟩ := hq t
          rw [show F (q y) = A y from hFp y.ofLp]
          simpa using hM y
      | succ k =>
        simpa [hzero] using (norm_nonneg _).trans (hM 0)
    · have hn : 0 < ‖v ν‖ := norm_pos_iff.2 hzero
      -- This shift negates the Fourier character at frequency ν.
      let d : EuclideanSpace ℝ (Fin n) := (2 * ‖v ν‖ ^ 2)⁻¹ • v ν
      have hd : ⟪v ν, d⟫ = (1 / 2 : ℝ) := by
        dsimp [d]
        rw [inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      have hdn : ‖d‖ = (2 * ‖v ν‖)⁻¹ := by
        dsimp [d]
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        field_simp
      have hu (t : UnitAddTorus (Fin n)) :
          UnitAddTorus.mFourier (-ν) (t + q d) = -UnitAddTorus.mFourier (-ν) t := by
        obtain ⟨y, rfl⟩ := hq t
        rw [← hqadd, hcharE, hcharE, inner_add_right]
        have hneg : v (-ν) = -v ν := by ext i; simp [v]
        rw [hneg, inner_neg_left _ d, hd, Complex.ofReal_add, mul_add, Complex.exp_add]
        have hexp : cexp (2 * π * I * ((-(1 / 2) : ℝ) : ℂ)) = -1 := by
          rw [show 2 * (π : ℂ) * I * ((-(1 / 2) : ℝ) : ℂ) = -(π * I) by push_cast; ring,
            Complex.exp_neg, Complex.exp_pi_mul_I]
          norm_num
        rw [hexp, mul_neg_one]
      have h := hcoeffBound ((fwdDiff (q d))^[k] F) ν (‖d‖ ^ k * M) fun t => by
        obtain ⟨y, rfl⟩ := hq t
        rw [hpull]
        exact norm_fwdDiff_iter_le d k hAk hM y
      rw [hdiff ν (q d) hu k F hF, norm_mul, norm_pow, hdn, inv_pow,
        le_inv_mul_iff₀ (by positivity), ← mul_assoc, ← mul_pow] at h
      have htwo : ‖(-2 : ℂ)‖ = 2 := by norm_num
      rwa [htwo, show 2 * ‖v ν‖ * 2 = 4 * ‖v ν‖ by ring] at h
  refine ⟨c, fun N => ?_, fun x => ?_⟩
  · obtain ⟨M₀, h₀⟩ := hbd 0
    obtain ⟨M, hM⟩ := hbd N
    refine ⟨2 ^ (N - 1) * (M₀ + n ^ N * M), fun ν => ?_⟩
    have hS0 : 0 ≤ ∑ k, |(ν k : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hS : ∑ k, |(ν k : ℝ)| ≤ n * (4 * ‖v ν‖) := by
      calc ∑ k, |(ν k : ℝ)| ≤ ∑ _k : Fin n, 4 * ‖v ν‖ := by
            refine Finset.sum_le_sum fun k _ => ?_
            have h1 : ‖(v ν).ofLp k‖ ≤ ‖v ν‖ := PiLp.norm_apply_le _ _
            have h2 : ‖(v ν).ofLp k‖ = |(ν k : ℝ)| := rfl
            linarith [norm_nonneg (v ν)]
        _ = _ := by simp
    have h1 := add_pow_le zero_le_one hS0 N
    have h2 : (∑ k, |(ν k : ℝ)|) ^ N ≤ n ^ N * (4 * ‖v ν‖) ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hS0 hS N
    have h3 := h₀ ν
    have h4 := mul_le_mul_of_nonneg_left (hM ν) (show (0 : ℝ) ≤ n ^ N by positivity)
    rw [pow_zero, one_mul] at h3
    rw [one_pow] at h1
    set a := ‖c ν‖
    have ha : 0 ≤ a := norm_nonneg _
    calc a * (1 + ∑ k, |(ν k : ℝ)|) ^ N
        ≤ a * (2 ^ (N - 1) * (1 + n ^ N * (4 * ‖v ν‖) ^ N)) := by
          refine mul_le_mul_of_nonneg_left (h1.trans ?_) ha
          gcongr
      _ = 2 ^ (N - 1) * (a + n ^ N * ((4 * ‖v ν‖) ^ N * a)) := by ring
      _ ≤ _ := by gcongr
  · have hdim : Module.finrank ℤ L = n := by
      rw [ZLattice.rank ℝ L, finrank_euclideanSpace_fin]
    obtain ⟨M, hM⟩ := hbd (n + 1)
    have hs₀ : Summable (fun ν => ‖v ν‖⁻¹ ^ (n + 1)) :=
      φ.summable_iff.2 (ZLattice.summable_norm_pow_inv L (n + 1) (by
        rw [hdim]
        exact Nat.lt_succ_self n))
    have hs : Summable c := by
      refine .of_norm_bounded_eventually (hs₀.mul_left ((4 : ℝ)⁻¹ ^ (n + 1) * M)) ?_
      filter_upwards [Filter.eventually_cofinite_ne (0 : Fin n → ℤ)] with ν hν
      have hv : 0 < ‖v ν‖ := norm_pos_iff.2 fun h => by
        apply hν
        apply φ.injective
        exact Subtype.ext (h.trans (show v 0 = 0 by ext i; simp [v]).symm)
      have h := hM ν
      rw [← le_inv_mul_iff₀ (by positivity), mul_pow, mul_inv] at h
      simpa only [inv_pow, mul_right_comm] using h
    have h := (UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := f) hs (p x)).tsum_eq
    exact (hFp x).symm.trans (h.symm.trans (tsum_congr fun ν => by
      rw [smul_eq_mul, hchar]))

end GlobalTheory
