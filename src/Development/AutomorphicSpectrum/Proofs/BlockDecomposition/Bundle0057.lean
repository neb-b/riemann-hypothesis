module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FaithfulIntegralClosure
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPderivNotDvd
section
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CompanionTheory.TraceJac

open MvPolynomial in
theorem exists_pderiv_not_dvd {K σ : Type*} [Field K] [CharZero K] (π : MvPolynomial σ K)
    (hπ : Prime π) : ∃ j, ¬ π ∣ pderiv j π := by
  classical
  have hT : π.totalDegree ≠ 0 := by
    intro h
    have hC := totalDegree_eq_zero_iff_eq_C.1 h
    by_cases ha : π.coeff 0 = 0
    · rw [ha, map_zero] at hC
      exact hπ.ne_zero hC
    · apply hπ.not_isUnit
      rw [hC]
      exact (IsUnit.mk0 _ ha).map C
  have h1 : ¬ ∀ m ∈ π.support, ∀ x, m x = 0 := by
    rwa [← totalDegree_eq_zero_iff]
  push Not at h1
  obtain ⟨m, hm, j, hj⟩ := h1
  refine ⟨j, fun hd => ?_⟩
  have hm' : (m - Finsupp.single j 1) + Finsupp.single j 1 = m := by
    ext i
    by_cases hi : i = j
    · subst hi
      simp
      omega
    · simp [Ne.symm hi]
  have hne : pderiv j π ≠ 0 := by
    intro h0
    have h2 := coeff_pderiv (i := j) π (m - Finsupp.single j 1)
    rw [h0, hm', AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h2
    have h3 : (((m - Finsupp.single j 1 : σ →₀ ℕ) j : ℕ) + 1 : K) ≠ 0 := by
      exact Nat.cast_add_one_ne_zero _
    exact mul_ne_zero (mem_support_iff.1 hm) h3 h2.symm
  obtain ⟨q, hq⟩ := hd
  have hq0 : q ≠ 0 := fun h => hne (by rw [hq, h, mul_zero])
  have hdeg : (pderiv j π).totalDegree = π.totalDegree + q.totalDegree := by
    rw [hq]; exact totalDegree_mul_of_isDomain hπ.ne_zero hq0
  have hlt : (pderiv j π).totalDegree < π.totalDegree := by
    have : (pderiv j π).totalDegree + 1 ≤ π.totalDegree := by
      have h4 : ∀ s ∈ (pderiv j π).support, s.sum (fun _ e => e) + 1 ≤ π.totalDegree := by
        intro s hs
        have h5 : s + Finsupp.single j 1 ∈ π.support := by
          rw [mem_support_iff] at hs ⊢
          intro h6
          apply hs
          rw [coeff_pderiv, h6, zero_mul]
        have := le_totalDegree h5
        rwa [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_single_index rfl] at this
      obtain ⟨s, hs, hs'⟩ : ∃ s ∈ (pderiv j π).support, (pderiv j π).totalDegree = s.sum (fun _ e => e) := by
        rw [totalDegree]
        obtain ⟨s, hs, hs'⟩ := Finset.exists_mem_eq_sup _ (support_nonempty.2 hne) (fun s : σ →₀ ℕ => s.sum fun _ e => e)
        exact ⟨s, hs, hs'⟩
      rw [hs']; exact h4 s hs
    omega
  omega

theorem finite_frac {A B F L : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.Finite A B] [Field F] [Field L] [Algebra A F] [IsFractionRing A F]
    [Algebra B L] [IsFractionRing B L] [Algebra F L] [Algebra A L] [IsScalarTower A F L]
    [IsScalarTower A B L] : FiniteDimensional F L := by
  classical
  obtain ⟨T, hT⟩ := (Module.Finite.fg_top : (⊤ : Submodule A B).FG)
  let W := IntermediateField.adjoin F ((T.image (algebraMap B L) : Finset L) : Set L)
  have hint : ∀ x ∈ ((T.image (algebraMap B L) : Finset L) : Set L), IsIntegral F x := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image] at hx
    obtain ⟨t, -, rfl⟩ := hx
    have h1 : IsIntegral A t := IsIntegral.of_finite A t
    exact (h1.algebraMap (B := L)).tower_top
  haveI : FiniteDimensional F W :=
    IntermediateField.finiteDimensional_adjoin hint
  have hB : ∀ x : B, algebraMap B L x ∈ W := by
    intro x
    have hx : x ∈ Submodule.span A (T : Set B) := hT ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem s hs =>
      refine IntermediateField.subset_adjoin _ _ ?_
      simp only [Finset.coe_image]
      exact ⟨s, hs, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact W.add_mem ha hb
    | smul r a _ ha =>
      have h1 : algebraMap B L (r • a) = algebraMap F L (algebraMap A F r) * algebraMap B L a := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
      rw [h1]
      exact W.mul_mem (W.algebraMap_mem _) ha
  have hW : W = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    exact W.div_mem (hB a) (hB s)
  have key : ∀ W' : IntermediateField F L, FiniteDimensional F W' → W' = ⊤ →
      FiniteDimensional F L := by
    rintro _ h rfl
    exact (IntermediateField.topEquiv (F := F) (E := L)).toLinearEquiv.finiteDimensional
  exact key W inferInstance hW

open Polynomial in
theorem integral_of_range {A R L : Type*} [CommRing A] [CommRing R] [Field L] [Algebra A L]
    [Algebra R L] (hr : ∀ a : A, algebraMap A L a ∈ (algebraMap R L).range) (x : L)
    (h : IsIntegral A x) : IsIntegral R x := by
  obtain ⟨p, hp, h0⟩ := h
  have hl : p.map (algebraMap A L) ∈ Polynomial.lifts (algebraMap R L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [coeff_map]
    exact hr _
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hp.map _)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, Polynomial.eval_map]
  exact h0

end GlobalTheory.CompanionTheory.TraceJac

namespace GlobalTheory.CompanionTheory.TraceJac

theorem at_prime_abs {P L F R n : Type*} [CommRing P] [IsDomain P] [IsNoetherianRing P] [Field L]
    [Field F] [CommRing R] [Algebra P R] [Algebra P F] [Algebra P L] [Algebra R F]
    [IsScalarTower P R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L] [IsScalarTower P R L]
    [IsFractionRing P F] [FiniteDimensional F L] [Algebra.IsSeparable F L] [Fintype n]
    [DecidableEq n] (π : P) (hπ : Prime π) (p : Ideal P) [p.IsPrime] (hp : p = Ideal.span {π})
    [IsLocalization.AtPrime R p] (E : n → Derivation ℤ L L)
    (hE : ∀ k f, ∃ f', E k (algebraMap P L f) = algebraMap P L f') (j : n) (fj : P)
    (hfj : E j (algebraMap P L π) = algebraMap P L fj) (hj : ¬ π ∣ fj)
    (hnat : ∀ m : ℕ, m ≠ 0 → IsUnit (m : R))
    (c : L) (hc : IsIntegral R c) (b : n → L) (hb : ∀ l, IsIntegral R (b l)) :
    ∃ f s : P, ¬ π ∣ s ∧
      algebraMap P F s * Algebra.trace F L (c * (Matrix.of fun k l => E k (b l)).det) =
        algebraMap P F f := by
  classical
  have hmem : ∀ s, s ∈ p ↔ π ∣ s := fun s => by rw [hp, Ideal.mem_span_singleton]
  have hmemM : ∀ s, s ∈ p.primeCompl ↔ ¬ π ∣ s := fun s => by
    rw [Ideal.mem_primeCompl_iff, hmem]
  haveI : IsDomain R := IsLocalization.isDomain_of_le_nonZeroDivisors R
    p.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing R := IsLocalization.isNoetherianRing p.primeCompl R inferInstance
  haveI : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R p
  haveI : IsFractionRing R F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl R F
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {algebraMap P R π} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p R, hp, Ideal.map_span, Set.image_singleton]
  have hπR0 : algebraMap P R π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    exact IsLocalization.injective R (M := p.primeCompl) p.primeCompl_le_nonZeroDivisors
      (h.trans (map_zero _).symm)
  have hnf : ¬ IsField R := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax]
    simpa using hπR0
  have hprin : (IsLocalRing.maximalIdeal R).IsPrincipal := ⟨⟨_, hmax⟩⟩
  haveI : IsDiscreteValuationRing R := by
    have h5 := (IsDiscreteValuationRing.TFAE R hnf).out 1 5
    exact h5.2 hprin
  have hirr : Irreducible (algebraMap P R π) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  have hρP : ∀ f, algebraMap R L (algebraMap P R f) = algebraMap P L f := fun f =>
    (IsScalarTower.algebraMap_apply P R L f).symm
  have hR : ∀ k (r : R), ∃ r' : R, E k (algebraMap R L r) = algebraMap R L r' := by
    intro k r
    obtain ⟨f, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl r
    have h1 := IsLocalization.mk'_spec R f s
    obtain ⟨w, hw⟩ := (IsLocalization.map_units R s).exists_right_inv
    obtain ⟨f1, hf1⟩ := hE k f
    obtain ⟨s1, hs1⟩ := hE k (s : P)
    refine ⟨(algebraMap P R f1 - IsLocalization.mk' R f s * algebraMap P R s1) * w, ?_⟩
    set x := algebraMap R L (IsLocalization.mk' R f s) with hx
    have h2 : x * algebraMap P L s = algebraMap P L f := by
      rw [hx, ← hρP, ← hρP, ← map_mul, h1]
    have h3 : algebraMap P L s * algebraMap R L w = 1 := by
      rw [← hρP, ← map_mul, hw, map_one]
    have h4 := congrArg (E k) h2
    rw [Derivation.leibniz, hf1, hs1] at h4
    simp only [smul_eq_mul] at h4
    rw [map_mul, map_sub, map_mul, hρP, hρP, ← hx, ← h4]
    linear_combination (-E k x) * h3
  obtain ⟨u, hu⟩ := IsLocalization.map_units R (⟨fj, (hmemM _).2 hj⟩ : p.primeCompl)
  obtain ⟨r, hr⟩ := trace_jac_dvr (F := F) hnat E hR (algebraMap P R π) hirr j u
    (by rw [hρP, hfj, hu, hρP]) c hc b hb
  obtain ⟨f, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl r
  refine ⟨f, s, (hmemM _).1 s.2, ?_⟩
  rw [← hr, IsScalarTower.algebraMap_apply P R F, IsScalarTower.algebraMap_apply P R F f,
    ← map_mul, mul_comm, IsLocalization.mk'_spec]

end GlobalTheory.CompanionTheory.TraceJac
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentialDecayByMidpoints
section
noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem exists_unit_mul_eq_abs (u : ℝ) : ∃ s : ℝ, |s| = 1 ∧ s * u = |u| := by
  by_cases h : 0 ≤ u
  · exact ⟨1, by simp, by rw [one_mul, abs_of_nonneg h]⟩
  · exact ⟨-1, by simp, by rw [abs_of_neg (not_le.1 h)]; ring⟩

theorem expDecay_of_midpoint : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type)
    [TopologicalSpace T] (φ : ℝ × ℝ → T → X) (S : Set (ℝ × ℝ)),
    (∀ a ∈ S, ∀ g : T, ∃ r : ℝ, 0 < r ∧ ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ x : ℝ × ℝ, |x.1 - a.1| ≤ r → |x.2 - a.2| ≤ r →
      ∀ g' ∈ U, ∀ t : ℝ × ℝ, ‖φ t g'‖ ≤ M * Real.exp (-rdot x t)) →
    (∀ x : ℝ × ℝ, ∃ a ∈ S, ∃ b ∈ S, x = midpoint ℝ a b) → ExpDecay φ := by
  intro X _ _ T _ φ S hS hmid x₀ g
  obtain ⟨a, ha, b, hb, hx₀⟩ := hmid x₀
  obtain ⟨ra, hra, Ua, hUa, Ma, hMa⟩ := hS a ha g
  obtain ⟨rb, hrb, Ub, hUb, Mb, hMb⟩ := hS b hb g
  have hm1 : a.1 + b.1 = 2 * x₀.1 := by rw [hx₀]; simp [midpoint_eq_smul_add]; ring
  have hm2 : a.2 + b.2 = 2 * x₀.2 := by rw [hx₀]; simp [midpoint_eq_smul_add]; ring
  refine ⟨min ra rb / 2, by positivity, Ua ∩ Ub, Filter.inter_mem hUa hUb, max (max Ma Mb) 0, ?_⟩
  intro x hx1 hx2 g' hg' t
  set ε := min ra rb / 2 with hε
  have hεa : 2 * ε ≤ ra := by rw [hε]; linarith [min_le_left ra rb]
  have hεb : 2 * ε ≤ rb := by rw [hε]; linarith [min_le_right ra rb]
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  obtain ⟨s1, hs1, hst1⟩ := exists_unit_mul_eq_abs t.1
  obtain ⟨s2, hs2, hst2⟩ := exists_unit_mul_eq_abs t.2
  have close : ∀ c d s : ℝ, |s| = 1 → |d| ≤ ε → |c + d + ε * s - c| ≤ 2 * ε := by
    intro c d s hs hd
    have hcd : c + d + ε * s - c = d + ε * s := by ring
    rw [hcd]
    calc |d + ε * s| ≤ |d| + |ε * s| := abs_add_le _ _
      _ = |d| + ε := by rw [abs_mul, hs, mul_one, abs_of_nonneg hε0]
      _ ≤ 2 * ε := by linarith
  have hA := hMa (a.1 + (x.1 - x₀.1) + ε * s1, a.2 + (x.2 - x₀.2) + ε * s2)
    ((close _ _ s1 hs1 hx1).trans hεa) ((close _ _ s2 hs2 hx2).trans hεa) g' hg'.1 t
  have hB := hMb (b.1 + (x.1 - x₀.1) + ε * s1, b.2 + (x.2 - x₀.2) + ε * s2)
    ((close _ _ s1 hs1 hx1).trans hεb) ((close _ _ s2 hs2 hx2).trans hεb) g' hg'.2 t
  set A := rdot (a.1 + (x.1 - x₀.1) + ε * s1, a.2 + (x.2 - x₀.2) + ε * s2) t with hAdef
  set B := rdot (b.1 + (x.1 - x₀.1) + ε * s1, b.2 + (x.2 - x₀.2) + ε * s2) t with hBdef
  have hsum : A + B = 2 * (rdot x t + ε * (|t.1| + |t.2|)) := by
    rw [hAdef, hBdef, ← hst1, ← hst2]
    simp only [rdot]
    linear_combination t.1 * hm1 + t.2 * hm2
  have hM0 : 0 ≤ max (max Ma Mb) 0 := le_max_right _ _
  have hR : max (max Ma Mb) 0 * Real.exp (-rdot x t) * Real.exp (-ε * (|t.1| + |t.2|)) =
      max (max Ma Mb) 0 * Real.exp (-((A + B) / 2)) := by
    rw [mul_assoc, ← Real.exp_add, hsum]
    congr 2
    ring
  rw [hR]
  rcases le_total B A with h | h
  · calc ‖φ t g'‖ ≤ Ma * Real.exp (-A) := hA
      _ ≤ max (max Ma Mb) 0 * Real.exp (-A) :=
          mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) (Real.exp_pos _).le
      _ ≤ max (max Ma Mb) 0 * Real.exp (-((A + B) / 2)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hM0
  · calc ‖φ t g'‖ ≤ Mb * Real.exp (-B) := hB
      _ ≤ max (max Ma Mb) 0 * Real.exp (-B) :=
          mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _)) (Real.exp_pos _).le
      _ ≤ max (max Ma Mb) 0 * Real.exp (-((A + B) / 2)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hM0

end GlobalTheory.CompanionTheory.TubeFourier
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentialFourierIntegralBound
section
noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem integral_exp_neg_mul_abs {ε : ℝ} (hε : 0 < ε) :
    ∫ u : ℝ, Real.exp (-ε * |u|) = 2 / ε := by
  have h := integral_comp_abs (f := fun x => Real.exp (-ε * x))
  rw [h, integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero]
  field_simp

theorem integrable_exp_neg_mul_abs {ε : ℝ} (hε : 0 < ε) :
    Integrable fun u : ℝ => Real.exp (-ε * |u|) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_exp_neg_mul_abs hε]
  positivity

theorem integrable_and_norm_integral_le (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X]
    (φ : ℝ × ℝ → X) (l : ℂ × ℂ) (ε M : ℝ) (hε : 0 < ε) (hφ : Continuous φ)
    (hb : ∀ t : ℝ × ℝ, ‖φ t‖ ≤ M * Real.exp (-rdot (l.1.re, l.2.re) t) *
      Real.exp (-ε * (|t.1| + |t.2|))) :
    Integrable (fun t : ℝ × ℝ => Complex.exp (dot l t) • φ t) ∧
      ‖∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t‖ ≤ M * (2 / ε) ^ 2 := by
  have hg1 := integrable_exp_neg_mul_abs hε
  have hgi : Integrable (fun t : ℝ × ℝ => M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|))) :=
    (hg1.mul_prod hg1).const_mul M
  have hbound : ∀ t : ℝ × ℝ, ‖Complex.exp (dot l t) • φ t‖ ≤
      M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|)) := by
    intro t
    rw [norm_smul, Complex.norm_exp]
    have hre : (dot l t).re = rdot (l.1.re, l.2.re) t := by simp [dot, rdot]
    rw [hre]
    have h1 : Real.exp (rdot (l.1.re, l.2.re) t) * Real.exp (-rdot (l.1.re, l.2.re) t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h2 : Real.exp (-ε * (|t.1| + |t.2|)) = Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|) := by
      rw [← Real.exp_add]; ring_nf
    calc Real.exp (rdot (l.1.re, l.2.re) t) * ‖φ t‖
        ≤ Real.exp (rdot (l.1.re, l.2.re) t) * (M * Real.exp (-rdot (l.1.re, l.2.re) t) *
          Real.exp (-ε * (|t.1| + |t.2|))) := mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos _).le
      _ = M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|)) := by
        rw [h2]
        linear_combination (M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|))) * h1
  have hc : Continuous (fun t : ℝ × ℝ => Complex.exp (dot l t) • φ t) := by
    have hd : Continuous (fun t : ℝ × ℝ => dot l t) := by simp only [dot]; fun_prop
    exact (Complex.continuous_exp.comp hd).smul hφ
  refine ⟨hgi.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hbound), ?_⟩
  calc ‖∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t‖
      ≤ ∫ t : ℝ × ℝ, M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|)) :=
        norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall hbound)
    _ = M * (2 / ε) ^ 2 := by
        rw [integral_const_mul, Measure.volume_eq_prod,
          integral_prod_mul (fun u : ℝ => Real.exp (-ε * |u|)) (fun u : ℝ => Real.exp (-ε * |u|)),
          integral_exp_neg_mul_abs hε]
        ring

end GlobalTheory.CompanionTheory.TubeFourier
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalFixedTensor
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ExtTensorFixed

variable {G H V W X ι : Type} [DecidableEq ι] [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]

theorem mem_fixed_iff (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) :
    v ∈ fixed ρ K ↔ ∀ k : K, ρ (k : G) v = v := by
  show (∀ h : K, ρ (h : G) v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v) ↔ _
  simp

theorem coord_lTensor (b : Module.Basis ι ℂ X) (f : W →ₗ[ℂ] W) (y : X ⊗[ℂ] W) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (f.lTensor X y) i =
      f (TensorProduct.equivFinsuppOfBasisLeft b y i) := by
  induction y with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul x w => simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]

theorem mem_range_lTensor_fixed (σ : Representation ℂ G W) (K : Subgroup G) (y : X ⊗[ℂ] W)
    (hy : ∀ k : K, (σ (k : G)).lTensor X y = y) :
    y ∈ LinearMap.range ((fixed σ K).subtype.lTensor X) := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ X
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := W) b
  have hc : ∀ i, e y i ∈ fixed σ K := fun i => (mem_fixed_iff σ K _).2 fun k => by
    have h := coord_lTensor b (σ (k : G)) y i
    rw [hy k] at h
    exact h.symm
  have hy' : y = (e y).sum fun i n => b i ⊗ₜ[ℂ] n := by
    have h : e.symm (e y) = _ := TensorProduct.equivFinsuppOfBasisLeft_symm_apply b (e y)
    exact (e.symm_apply_apply y).symm.trans h
  rw [hy']
  refine Submodule.sum_mem _ fun i _ => ⟨b i ⊗ₜ[ℂ] (⟨e y i, hc i⟩ : fixed σ K), ?_⟩
  simp

theorem fixed_le_range (ρ : Representation ℂ G V) (σ : Representation ℂ H W)
    (K₁ : Subgroup G) (K₂ : Subgroup H) :
    fixed (extTensor ρ σ) (K₁.prod K₂) ≤
      LinearMap.range (TensorProduct.map (fixed ρ K₁).subtype (fixed σ K₂).subtype) := by
  intro x hx
  have hx' := (mem_fixed_iff _ _ _).1 hx
  have act : ∀ (g : G × H) (z : V ⊗[ℂ] W),
      extTensor ρ σ g z = TensorProduct.map (ρ g.1) (σ g.2) z := by
    intro g z
    induction z with
    | add a c ha hc => simp [ha, hc]
    | tmul v w => simp

  have h1 : ∀ k : K₁, (ρ (k : G)).lTensor W (TensorProduct.comm ℂ V W x) =
      TensorProduct.comm ℂ V W x := by
    intro k
    have hk := hx' ⟨((k : G), 1), ⟨k.2, one_mem _⟩⟩
    rw [act] at hk
    conv_rhs => rw [← hk]
    simp only [map_one]
    generalize x = z
    induction z with
    | add a c ha hc => simp only [map_add (f := _), ha, hc]
    | tmul v w => simp
  obtain ⟨y', hy'⟩ := mem_range_lTensor_fixed ρ K₁ _ h1
  let y : (fixed ρ K₁) ⊗[ℂ] W := TensorProduct.comm ℂ W (fixed ρ K₁) y'
  have hy : (fixed ρ K₁).subtype.rTensor W y = x := by
    have : (fixed ρ K₁).subtype.rTensor W y =
        TensorProduct.comm ℂ W V ((fixed ρ K₁).subtype.lTensor W y') := by
      simp only [y]
      generalize y' = z
      induction z with
      | add a c ha hc => simp only [map_add (f := _), ha, hc]
      | tmul v w => simp
    rw [this, hy']
    simp

  have hinj : Function.Injective ((fixed ρ K₁).subtype.rTensor W) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  have h2 : ∀ k : K₂, (σ (k : H)).lTensor (fixed ρ K₁) y = y := by
    intro k
    apply hinj
    have hk := hx' ⟨(1, (k : H)), ⟨one_mem _, k.2⟩⟩
    rw [act] at hk
    rw [hy]
    conv_rhs => rw [← hk, ← hy]
    simp only [map_one]
    generalize y = z
    induction z with
    | add a c ha hc => simp only [map_add (f := _), ha, hc]
    | tmul v w => simp
  obtain ⟨z, hz⟩ := mem_range_lTensor_fixed σ K₂ y h2
  refine ⟨z, ?_⟩
  rw [← hy, ← hz]
  generalize z = t
  induction t with
  | add a c ha hc => simp only [map_add (f := _), ha, hc]
  | tmul v w => simp

theorem finiteDimensional_fixed_extTensor : ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V)
    (σ : Representation ℂ H W) (K₁ : Subgroup G) (K₂ : Subgroup H),
    FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K₁) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed σ K₂) →
    FiniteDimensional ℂ (GlobalTheory.PRep.fixed (GlobalTheory.SmGL.extTensor ρ σ) (K₁.prod K₂)) := by
  intro G H V W _ _ _ _ _ _ ρ σ K₁ K₂ h₁ h₂
  exact Submodule.finiteDimensional_of_le (fixed_le_range ρ σ K₁ K₂)

end GlobalTheory.CompanionTheory.ExtTensorFixed
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModuleAdicComplete
section
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.FiniteComplete

theorem isAdicComplete_of_finite : ∀ (O M : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [AddCommGroup M] [Module O M]
    [Module.Finite O M], IsAdicComplete (IsLocalRing.maximalIdeal O) M := by
  intro O M _ _ _ hO _ _ _
  set I := IsLocalRing.maximalIdeal O
  have hb : Function.Bijective (AdicCompletion.of I O) := AdicCompletion.of_bijective_iff.2 hO
  let φ : O ≃ₗ[O] AdicCompletion I O := LinearEquiv.ofBijective (AdicCompletion.of I O) hb
  let e : M ≃ₗ[O] AdicCompletion I O ⊗[O] M :=
    (TensorProduct.lid O M).symm.trans (TensorProduct.congr φ (LinearEquiv.refl O M))
  have h1 : AdicCompletion.of I O 1 = 1 := by
    ext n
    simp
  have hfac : ⇑(AdicCompletion.of I M) = ⇑(AdicCompletion.ofTensorProduct I M) ∘ ⇑e := by
    funext m
    have he : e m = (1 : AdicCompletion I O) ⊗ₜ[O] m := by
      simp [e, φ, h1]
    simp [he]
  refine AdicCompletion.of_bijective_iff.1 ?_
  rw [hfac]
  exact (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I M).comp e.bijective

end GlobalTheory.CompanionTheory.FiniteComplete
end

