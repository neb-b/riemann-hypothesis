module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

section Chart

variable (o : Type*) {Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {ι : Type*}

def chartRing (x : ι → Ω) (i : ι) : Subalgebra o Ω :=
  Algebra.adjoin o (Set.range fun j => x j / x i)

structure ChartBundle (x : ι → Ω) (r : ℕ) (E : Type*) [AddCommGroup E] [Module Ω E] where

  lat : ι → AddSubgroup E

  stable : ∀ i, ∀ a ∈ chartRing o x i, ∀ e ∈ lat i, a • e ∈ lat i

  frame : ∀ i, x i ≠ 0 → ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing o x i) ∧
    (∀ l, c l ∈ chartRing o x i) ∧ ∑ l, c l * f l = 1 ∧
    ∀ l, ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, f l ^ n • e ∈ lat i) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing o x i) ∧ e = ∑ q, a q • b q

  overlap : ∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ lat i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ lat j

variable {o}

theorem div_mem_chartRing (x : ι → Ω) (i j : ι) :
    x j / x i ∈ chartRing o x i :=
  Algebra.subset_adjoin ⟨j, rfl⟩

theorem exists_pow_mul_mem_chartRing (x : ι → Ω) (i j : ι) (hi : x i ≠ 0)
    {a : Ω} (ha : a ∈ chartRing o x i) :
    ∃ m : ℕ, (x i / x j) ^ m * a ∈ chartRing o x j := by
  have hij : x i / x j ∈ chartRing o x j := div_mem_chartRing x j i
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    refine ⟨1, ?_⟩
    have : x i / x j * (x k / x i) = x k / x j := by field_simp
    rw [pow_one, this]
    exact div_mem_chartRing x j k
  | algebraMap r =>
    exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : (x i / x j) ^ (m + n) * (y + z) =
        (x i / x j) ^ n * ((x i / x j) ^ m * y) + (x i / x j) ^ m * ((x i / x j) ^ n * z) := by
      ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hij _) hm) (mul_mem (pow_mem hij _) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : (x i / x j) ^ (m + n) * (y * z) = ((x i / x j) ^ m * y) * ((x i / x j) ^ n * z) := by
      ring
    rw [this]
    exact mul_mem hm hn

variable (o)

def lineLat (x : ι → Ω) (d : ℕ) (i : ι) : AddSubgroup Ω :=
  ((Subalgebra.toSubmodule (chartRing o x i)).map (LinearMap.mulRight o (x i ^ d))).toAddSubgroup

variable {o}

theorem mem_lineLat (x : ι → Ω) (d : ℕ) (i : ι) (e : Ω) :
    e ∈ lineLat o x d i ↔ ∃ a ∈ chartRing o x i, a * x i ^ d = e := by
  simp [lineLat]

variable (o)

def lineBundle (x : ι → Ω) (d : ℕ) : ChartBundle o x 1 Ω where
  lat := lineLat o x d
  stable i a ha e he := by
    obtain ⟨c, hc, rfl⟩ := (mem_lineLat x d i e).1 he
    refine (mem_lineLat x d i _).2 ⟨a * c, mul_mem ha hc, ?_⟩
    rw [smul_eq_mul, mul_assoc]
  frame i hi := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
    simp only [one_pow, one_smul, one_mul, exists_const]
    refine ⟨fun _ => x i ^ d, ?_, ?_, ?_⟩
    · rw [linearIndependent_unique_iff]
      exact pow_ne_zero _ hi
    · rw [Set.range_const]
      exact Ideal.span_singleton_eq_top.2 (isUnit_iff_ne_zero.2 (pow_ne_zero _ hi))
    · intro e
      rw [mem_lineLat]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨fun _ => a, fun _ => ha, by simp⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a 0, ha 0, by simp⟩
  overlap i j hi hj e he := by
    obtain ⟨a, ha, rfl⟩ := (mem_lineLat x d i e).1 he
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_chartRing x i j hi ha
    refine ⟨m, (mem_lineLat x d j _).2 ⟨(x i / x j) ^ m * a * (x i / x j) ^ d,
      mul_mem hm (pow_mem (div_mem_chartRing x j i) _), ?_⟩⟩
    rw [smul_eq_mul, div_pow, div_pow]
    field_simp

end Chart

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.FsMetricFinIsSemipositive
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

variable {ι : Type*} [Fintype ι]

def fsLp (ι : Type*) [Fintype ι] : (ι → ℂ) →L[ℝ] EuclideanSpace ℂ ι :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).symm :
    (ι → ℂ) →L[ℂ] EuclideanSpace ℂ ι).restrictScalars ℝ

lemma fsLp_apply (z : ι → ℂ) : fsLp ι z = WithLp.toLp 2 z := rfl

lemma fsLp_ne_zero {z : ι → ℂ} (hz : z ≠ 0) : fsLp ι z ≠ 0 := by
  rw [fsLp_apply]
  intro h
  apply hz
  have h2 := congrArg (WithLp.ofLp (p := 2)) h
  simpa using h2

lemma fsLp_smul_I (w : ι → ℂ) : fsLp ι (Complex.I • w) = Complex.I • fsLp ι w := rfl

lemma fsLp_normSq_ne_zero {z : ι → ℂ} (hz : z ≠ 0) : ‖fsLp ι z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (fsLp_ne_zero hz))

def fsGrad (y : ι → ℂ) : (ι → ℂ) →L[ℝ] ℝ :=
  (‖fsLp ι y‖ ^ 2)⁻¹ • (innerSL ℝ (fsLp ι y)).comp (fsLp ι)

lemma fsGrad_apply (y v : ι → ℂ) :
    fsGrad y v = (‖fsLp ι y‖ ^ 2)⁻¹ * inner ℝ (fsLp ι y) (fsLp ι v) := rfl

lemma hasFDerivAt_logFs {y : ι → ℂ} (hy : y ≠ 0) :
    HasFDerivAt (fun z => Real.log ‖fsLp ι z‖) (fsGrad y) y := by
  have h0 : fsLp ι y ≠ 0 := fsLp_ne_zero hy
  have hL : HasFDerivAt (fsLp ι) (fsLp ι) y := (fsLp ι).hasFDerivAt
  have h1 := (HasFDerivAt.log (HasFDerivAt.norm_sq hL) (fsLp_normSq_ne_zero hy)).const_mul (1 / 2 : ℝ)
  have hfun : (fun z => Real.log ‖fsLp ι z‖) = fun z => 1 / 2 * Real.log (‖fsLp ι z‖ ^ 2) := by
    funext z
    rw [Real.log_pow]
    push_cast
    ring
  rw [hfun]
  refine h1.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  rw [fsGrad_apply]
  simp
  ring

lemma fderiv_logFs_eventuallyEq {z : ι → ℂ} (hz : z ≠ 0) :
    fderiv ℝ (fun z => Real.log ‖fsLp ι z‖) =ᶠ[nhds z] fsGrad := by
  filter_upwards [eventually_ne_nhds hz] with y hy using (hasFDerivAt_logFs hy).fderiv

lemma hess_logFs {z : ι → ℂ} (hz : z ≠ 0) (w : ι → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z => Real.log ‖fsLp ι z‖)) z w w =
      ‖fsLp ι w‖ ^ 2 / ‖fsLp ι z‖ ^ 2 -
        2 * inner ℝ (fsLp ι z) (fsLp ι w) ^ 2 / (‖fsLp ι z‖ ^ 2) ^ 2 := by
  have hL : HasFDerivAt (fsLp ι) (fsLp ι) z := (fsLp ι).hasFDerivAt
  have h0 := fsLp_normSq_ne_zero hz
  have hc := (hasDerivAt_inv h0).comp_hasFDerivAt z (HasFDerivAt.norm_sq hL)
  have hT : HasFDerivAt (fun y => (innerSL ℝ (fsLp ι y)).comp (fsLp ι))
      (((ContinuousLinearMap.compL ℝ (ι → ℂ) (EuclideanSpace ℂ ι) ℝ).flip (fsLp ι)).comp
      ((innerSL ℝ).comp (fsLp ι))) z :=
    (((ContinuousLinearMap.compL ℝ (ι → ℂ) (EuclideanSpace ℂ ι) ℝ).flip (fsLp ι)).comp
      ((innerSL ℝ).comp (fsLp ι))).hasFDerivAt
  have hG := HasFDerivAt.smul hc hT
  rw [(fderiv_logFs_eventuallyEq hz).fderiv_eq]
  have hfG : (fsGrad (ι := ι)) = ((fun y : ℝ => y⁻¹) ∘ fun x => ‖fsLp ι x‖ ^ 2) •
      (fun y => (innerSL ℝ (fsLp ι y)).comp (fsLp ι)) := rfl
  rw [hfG, hG.fderiv]
  simp
  field_simp
  ring

lemma inner_sq_add_inner_I_sq (x y : EuclideanSpace ℂ ι) :
    inner ℝ x y ^ 2 + inner ℝ x (Complex.I • y) ^ 2 = ‖inner ℂ x y‖ ^ 2 := by
  have e0 : ∀ u v : EuclideanSpace ℂ ι, inner ℝ u v = (inner ℂ u v).re := by
    intro u v
    rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    first
    | rfl
    | simp [Complex.inner, RCLike.inner_apply]
    | simp [Complex.inner, mul_comm]
  rw [e0, e0, inner_smul_right, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re,
    Complex.I_re, Complex.I_im]
  ring

theorem fsMetric_isSmooth : IsSmoothMetric (fsMetric (ι := ι)) := by
  intro z hz
  change ContDiffWithinAt ℝ _ (fun z => ‖fsLp ι z‖) _ z
  have h0 : fsLp ι z ≠ 0 := fsLp_ne_zero hz
  have hn : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : EuclideanSpace ℂ ι => ‖u‖) (fsLp ι z) := by
    first
    | exact contDiffAt_norm ℝ h0
    | exact contDiffAt_norm h0
  exact (hn.comp z (fsLp ι).contDiff.contDiffAt).contDiffWithinAt

theorem leviForm_fsMetric {z : ι → ℂ} (hz : z ≠ 0) (w : ι → ℂ) :
    leviForm (fun z => Real.log ((fsMetric (ι := ι)).ρ z)) z w =
      (‖fsLp ι w‖ ^ 2 * ‖fsLp ι z‖ ^ 2 - ‖inner ℂ (fsLp ι z) (fsLp ι w)‖ ^ 2) /
        (2 * (‖fsLp ι z‖ ^ 2) ^ 2) := by
  change leviForm (fun z => Real.log ‖fsLp ι z‖) z w = _
  unfold leviForm
  rw [hess_logFs hz, hess_logFs hz, fsLp_smul_I, norm_smul, Complex.norm_I, one_mul,
    ← inner_sq_add_inner_I_sq]
  have h0 := fsLp_normSq_ne_zero hz
  field_simp
  ring

theorem fsMetric_isSemipositive : IsSemipositive (fsMetric (ι := ι)) := by
  refine ⟨fsMetric_isSmooth, fun z hz w => ?_⟩
  rw [leviForm_fsMetric hz]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (fsLp ι z) (fsLp ι w)
  have h2 := mul_self_le_mul_self (norm_nonneg _) hcs
  apply div_nonneg
  · nlinarith [h2]
  · positivity

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAC
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF

open Ideal

theorem height_polynomial_of_isMaximal {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsJacobsonRing R] {c : ℕ∞} (hR : ∀ m : Ideal R, m.IsMaximal → m.height = c)
    (M : Ideal (Polynomial R)) (hM : M.IsMaximal) : M.height = c + 1 := by
  haveI := hM
  have hp : (M.under R).IsMaximal := by
    rw [Ideal.under, Polynomial.algebraMap_eq]
    exact Polynomial.isMaximal_comap_C_of_isJacobsonRing M
  haveI : M.LiesOver (M.under R) := ⟨rfl⟩
  rw [Polynomial.height_eq_height_add_one (M.under R) M, hR _ hp]

theorem height_mvPolynomial_fin_of_isMaximal {k : Type*} [Field k] :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)), M.IsMaximal → M.height = n
  := by
    intro n
    induction n with
    | zero =>
      intro M hM
      have h := Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
      rw [ringKrullDim_mvPolynomial_of_isEmpty, ringKrullDim_eq_zero_of_field] at h
      rw [Nat.cast_zero]
      exact le_antisymm (WithBot.coe_le_coe.mp h) zero_le
    | succ n ih =>
      intro M hM
      let e := (MvPolynomial.finSuccEquiv k n).toRingEquiv
      have hM' : (M.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
      rw [← e.height_map M, height_polynomial_of_isMaximal ih _ hM']
      simp

theorem height_map_under_eq_zero {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.IsIntegral R B] (M : Ideal B) [M.IsPrime] :
    (M.map (Ideal.Quotient.mk ((M.under R).map (algebraMap R B)))).height = 0 := by
  classical
  have hIM : (M.under R).map (algebraMap R B) ≤ M := Ideal.map_comap_le
  set I := (M.under R).map (algebraMap R B) with hIdef
  haveI hp : (M.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIM)
  have hMc : (M.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = M := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hIM]
  have h0 : M.map (Ideal.Quotient.mk I) ∈ minimalPrimes (B ⧸ I) := by
    refine ⟨⟨hp, bot_le⟩, ?_⟩
    intro Q hQ hQM
    haveI hQp : Q.IsPrime := hQ.1
    set Q' := Q.comap (Ideal.Quotient.mk I) with hQ'def
    have hQ'M : Q' ≤ M := by
      rw [← hMc]
      exact Ideal.comap_mono hQM
    have hIQ' : I ≤ Q' := by
      intro x hx
      rw [hQ'def, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact Q.zero_mem
    have hQ'eq : Q' = M := by
      by_contra hne
      have hlt : Q' < M := lt_of_le_of_ne hQ'M hne
      obtain ⟨x, hxM, hxQ⟩ := SetLike.exists_of_lt hlt
      have hcl := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := R) hQ'M ⟨hxM, hxQ⟩
        (Algebra.IsIntegral.isIntegral x)
      have hge : M.under R ≤ Q'.comap (algebraMap R B) :=
        (Ideal.le_comap_map).trans (Ideal.comap_mono hIQ')
      exact absurd (lt_of_le_of_lt hge hcl) (lt_irrefl _)
    have hmq : M.map (Ideal.Quotient.mk I) = Q := by
      rw [← hQ'eq, hQ'def, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    exact hmq.le
  exact Ideal.height_eq_zero_iff.mpr h0

theorem exists_height_of_isMaximal_of_field (k B : Type*) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] :
    ∃ s : ℕ, ∀ M : Ideal B, M.IsMaximal → M.height = s := by
  classical
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k B
  letI : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) B := hfin
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := Algebra.IsIntegral.of_finite _ _
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) B := (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  refine ⟨s, fun M hM => ?_⟩
  haveI := hM
  haveI hmax : (M.under (MvPolynomial (Fin s) k)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
  haveI : M.LiesOver (M.under (MvPolynomial (Fin s) k)) := ⟨rfl⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (M.under (MvPolynomial (Fin s) k)) M,
    height_mvPolynomial_fin_of_isMaximal s _ hmax, height_map_under_eq_zero M, add_zero]

end ReciprocityTheory.ChartRestriction.G.Geo.DimF
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFS
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem maDensity_congr_of_eventuallyEq {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ j, φ j =ᶠ[𝓝 y] ψ j) : maDensity φ y = maDensity ψ y := by
  have h2 : ∀ j, fderiv ℝ (fderiv ℝ (φ j)) y = fderiv ℝ (fderiv ℝ (ψ j)) y := fun j =>
    Filter.EventuallyEq.fderiv_eq (show fderiv ℝ (φ j) =ᶠ[𝓝 y] fderiv ℝ (ψ j) from
      (h j).eventuallyEq_nhds.mono fun _ h' => h'.fderiv_eq)
  have hH : ∀ k, cxHessian (φ k) y = cxHessian (ψ k) y := by
    intro k
    unfold cxHessian
    rw [h2 k]
  simp only [maDensity, hH]

theorem mixedDisc_one (A : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ) : mixedDisc A = A 0 0 0 := by
  unfold mixedDisc
  rw [← Finset.powerset_univ, Finset.univ_unique, ← Finset.insert_empty,
    Finset.sum_powerset_insert (by simp)]
  simp [Matrix.det_unique]

theorem maDensity_one (f : (Fin 1 → ℂ) → ℝ) (y : Fin 1 → ℂ) :
    maDensity (fun _ => f) y = (fderiv ℝ (fderiv ℝ f) y (Pi.single 0 1) (Pi.single 0 1) +
      fderiv ℝ (fderiv ℝ f) y (Complex.I • Pi.single 0 1) (Complex.I • Pi.single 0 1)) /
        (2 * Real.pi) := by
  have hre : ∀ u v : ℝ, ((((u : ℂ) + Complex.I * (v : ℂ)) / 4).re) = u / 4 := by
    intro u v
    simp [Complex.div_ofNat_re]
  rw [maDensity, mixedDisc_one]
  simp only [cxHessian, hre]
  have := Real.pi_pos
  simp
  field_simp
  ring

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

section Coord

variable (o : Type*) {Ω : Type*} [CommRing o] [CommRing Ω] [Algebra o Ω] {ι : Type*}

private theorem coneMap_monomial' (x : ι → Ω) (e : ι →₀ ℕ) (a : o) :
    coneMap o x (monomial e a) = Polynomial.C (aeval x (monomial e a)) * Polynomial.X ^ e.degree := by
  unfold coneMap
  rw [aeval_monomial, aeval_monomial, Polynomial.algebraMap_apply, map_mul, mul_assoc]
  congr 1
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, Polynomial.C_pow,
    Finset.prod_pow_eq_pow_sum]
  congr 1

private theorem coeff_coneMap_eq_aeval_homogeneousComponent (x : ι → Ω) (f : MvPolynomial ι o) (d : ℕ) :
    (coneMap o x f).coeff d = aeval x (homogeneousComponent d f) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [f.as_sum, map_sum]
  rw [Polynomial.finsetSum_coeff]
  simp only [coneMap_monomial', Polynomial.coeff_C_mul_X_pow]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [homogeneousComponent_apply, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases eq_or_ne e.degree d with h | h
  · simp [h]
  · rw [if_neg (Ne.symm h), if_neg h]

theorem coneMap_of_isHomogeneous (x : ι → Ω) {f : MvPolynomial ι o} {n : ℕ}
    (hf : f.IsHomogeneous n) :
    coneMap o x f = Polynomial.C (aeval x f) * Polynomial.X ^ n := by
  ext d
  rw [coeff_coneMap_eq_aeval_homogeneousComponent, Polynomial.coeff_C_mul_X_pow,
    homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hf)]
  rcases eq_or_ne d n with rfl | h
  · simp
  · rw [if_neg h, if_neg h, map_zero]

theorem mem_coordIdeal_of_isHomogeneous (x : ι → Ω) {f : MvPolynomial ι o} {n : ℕ}
    (hf : f.IsHomogeneous n) (h : aeval x f = 0) : f ∈ coordIdeal o x := by
  rw [coordIdeal, RingHom.mem_ker, coneMap_of_isHomogeneous o x hf, h, map_zero, zero_mul]

theorem coeff_coneMap (x : ι → Ω) (f : MvPolynomial ι o) (d : ℕ) :
    (coneMap o x f).coeff d = aeval x (homogeneousComponent d f) := by
  exact coeff_coneMap_eq_aeval_homogeneousComponent o x f d

theorem coordIdeal_isHomogIdeal (x : ι → Ω) : IsHomogIdeal o (coordIdeal o x) := by
  intro f hf d
  rw [coordIdeal, RingHom.mem_ker] at hf ⊢
  rw [coneMap_of_isHomogeneous o x (homogeneousComponent_isHomogeneous d f), ← coeff_coneMap, hf,
    Polynomial.coeff_zero, map_zero, zero_mul]

end Coord

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemSec
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

section LemSec

variable (o : Type*) {Ω : Type*} [CommRing o] [CommRing Ω] [Algebra o Ω] {ι : Type*}

theorem coordIdeal_isPrime [IsDomain Ω] (x : ι → Ω) : (coordIdeal o x).IsPrime :=
  RingHom.ker_isPrime _

end LemSec

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.PenVol
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial Filter

section Vol

variable {o : Type*} [CommRing o] {Ω : Type*} [CommRing Ω] [Algebra o Ω] {ι : Type*}

def smallSectionCount (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (τ : ℕ) : ℝ :=
  Real.log (Nat.card {s : La τ // P τ (s : Ω)})

def arVolP (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (a D : ℕ) : ℝ :=
  limsup (fun k : ℕ => smallSectionCount P La (a * k) /
    (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop

end Vol

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

