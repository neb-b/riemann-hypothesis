module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ConjTransposeBoostMulSignatureMulBoost
section
open Matrix WithLp
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace GlobalTheory
namespace MatrixBall

section general

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
lemma norm_toEuclideanLin_le (M : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ‖toEuclideanLin M x‖ ≤ ‖M‖ * ‖x‖ :=
  M.l2_opNorm_mulVec x

lemma dotProduct_mulVec_eq_inner (M : Matrix n n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ M *ᵥ v = ⟪(toLp 2 v : EuclideanSpace ℂ n), toEuclideanLin M (toLp 2 v)⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

lemma inner_conjTranspose_mul (M N : Matrix m n ℂ) (x y : EuclideanSpace ℂ n) :
    ⟪x, toEuclideanLin (Mᴴ * N) y⟫_ℂ = ⟪toEuclideanLin M x, toEuclideanLin N y⟫_ℂ := by
  rw [toLpLin_mul (q := 2), LinearMap.comp_apply, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_right]

lemma inner_one_sub (M : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ⟪x, toEuclideanLin (1 - Mᴴ * M) x⟫_ℂ = ((‖x‖ ^ 2 - ‖toEuclideanLin M x‖ ^ 2 : ℝ) : ℂ) := by
  rw [map_sub, LinearMap.sub_apply, inner_sub_right, inner_conjTranspose_mul, toLpLin_one,
    LinearMap.id_apply, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp

omit [DecidableEq n] in
lemma isHermitian_one_sub [DecidableEq n] (M : Matrix m n ℂ) : (1 - Mᴴ * M).IsHermitian :=
  isHermitian_one.sub (isHermitian_conjTranspose_mul_self M)

lemma posDef_one_sub_conjTranspose_mul {Z : Matrix m n ℂ} (hZ : ‖Z‖ < 1) :
    (1 - Zᴴ * Z).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (isHermitian_one_sub Z) fun v hv => ?_
  rw [dotProduct_mulVec_eq_inner, inner_one_sub]
  have hx : 0 < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ := by
    rw [norm_pos_iff]; intro h; exact hv (by simpa using h)
  have h1 := norm_toEuclideanLin_le Z (toLp 2 v)
  have h2 : ‖toEuclideanLin Z (toLp 2 v)‖ < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ := by nlinarith
  have h3 := norm_nonneg (toEuclideanLin Z (toLp 2 v))
  exact_mod_cast (by nlinarith : (0 : ℝ) < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 -
    ‖toEuclideanLin Z (toLp 2 v)‖ ^ 2)

theorem norm_lt_one_of_posDef {Z : Matrix m n ℂ} (hP : (1 - Zᴴ * Z).PosDef) : ‖Z‖ < 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have : Z = 0 := by ext i j; exact hn.elim j
    simp [this]
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ n) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 zero_le_one)
    (f := fun x => ‖toEuclideanLin Z x‖)
    ((toEuclideanLin Z).continuous_of_finiteDimensional.norm.continuousOn)
  have hx1 : ‖x‖ = 1 := by simpa using hx
  have hx0 : ofLp x ≠ 0 := by
    intro h
    have : x = 0 := by simpa using h
    simp [this] at hx1
  have h1 := hP.dotProduct_mulVec_pos hx0
  rw [dotProduct_mulVec_eq_inner, inner_one_sub, toLp_ofLp, hx1] at h1
  have h2 : (0 : ℝ) < 1 ^ 2 - ‖toEuclideanLin Z x‖ ^ 2 := by exact_mod_cast h1
  have h3 := norm_nonneg (toEuclideanLin Z x)
  have h4 : ‖toEuclideanLin Z x‖ < 1 := by nlinarith
  refine lt_of_le_of_lt ?_ h4
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm h3 fun y hy => ?_
  exact hmax (by simpa using hy)

theorem posDef_iff_norm_lt_one (Z : Matrix m n ℂ) : (1 - Zᴴ * Z).PosDef ↔ ‖Z‖ < 1 :=
  ⟨norm_lt_one_of_posDef, posDef_one_sub_conjTranspose_mul⟩

end general

section hermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

end hermitian

section boost

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

def invSqrt {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) : Matrix n n ℂ :=
  (CFC.sqrt M)⁻¹

def boost (Z : Matrix p q ℂ) : Matrix (p ⊕ q) (p ⊕ q) ℂ :=
  fromBlocks (invSqrt (1 - Z * Zᴴ)) (Z * invSqrt (1 - Zᴴ * Z))
    (Zᴴ * invSqrt (1 - Z * Zᴴ)) (invSqrt (1 - Zᴴ * Z))

section invSqrt

variable {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}

end invSqrt

variable {Z : Matrix p q ℂ}

end boost

end MatrixBall

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
section
open MeasureTheory Set
open scoped ENNReal Pointwise

namespace GlobalTheory

section Multiplicity

variable {G X : Type*} [Group G] [MulAction G X]

variable [MeasurableSpace X] {μ : Measure X} [MeasurableConstSMul G X]
  [SMulInvariantMeasure G X μ] [Countable G] {B D : Set X}


@[to_additive
]
theorem tsum_indicator_smul_eq_encard (B : Set X) (x : X) :
    ∑' g : G, ((fun y => g • y) ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) x
      = ({g : G | g • x ∈ B}.encard : ℝ≥0∞) := by
  rw [← ENNReal.tsum_set_one, tsum_subtype {g : G | g • x ∈ B} (fun _ => (1 : ℝ≥0∞))]
  refine tsum_congr fun g => ?_
  by_cases h : g • x ∈ B <;> simp [Set.indicator, h]

@[to_additive
]
theorem sum_restrict_preimage_smul_le (hB : NullMeasurableSet B μ) {m : ℝ≥0∞}
    (hm : ∀ᵐ x ∂μ.restrict D, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    (Measure.sum fun g : G => (μ.restrict D).restrict ((fun y => g • y) ⁻¹' B))
      ≤ m • μ.restrict D := by
  have hB' : ∀ g : G, NullMeasurableSet ((fun y => g • y) ⁻¹' B) (μ.restrict D) := fun g =>
    (hB.preimage (measurePreserving_smul g μ).quasiMeasurePreserving).mono
      Measure.restrict_le_self
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.sum_apply _ hA, Measure.smul_apply, smul_eq_mul]
  have h1 : ∀ g : G, ((μ.restrict D).restrict ((fun y => g • y) ⁻¹' B)) A
      = ∫⁻ x in A, ((fun y => g • y) ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) x
          ∂(μ.restrict D) := by
    intro g
    rw [lintegral_indicator₀ ((hB' g).mono Measure.restrict_le_self), setLIntegral_one,
      Measure.restrict_apply hA,
      Measure.restrict_apply₀ ((hB' g).mono Measure.restrict_le_self), inter_comm]
  simp_rw [h1]
  rw [← lintegral_tsum fun g => (aemeasurable_const.indicator₀
    ((hB' g).mono Measure.restrict_le_self))]
  simp_rw [tsum_indicator_smul_eq_encard]
  calc ∫⁻ x in A, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ∂(μ.restrict D)
      ≤ ∫⁻ _ in A, m ∂(μ.restrict D) := lintegral_mono_ae (ae_restrict_of_ae hm)
    _ = m * (μ.restrict D) A := by rw [setLIntegral_const]

@[to_additive setLIntegral_le_mul_of_ae_covers_vadd
]
theorem setLIntegral_le_mul_of_ae_covers (hD : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D)
    (hB : NullMeasurableSet B μ) {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x)
    {m : ℝ≥0∞} (hm : ∀ᵐ x ∂μ.restrict D, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    ∫⁻ x in B, u x ∂μ ≤ m * ∫⁻ x in D, u x ∂μ := by
  have hcov : B ≤ᵐ[μ] (⋃ g : G, g • (((fun y => g • y) ⁻¹' B) ∩ D) : Set X) := by
    filter_upwards [hD] with x ⟨g, hg⟩ hx
    refine mem_iUnion.2 ⟨g⁻¹, g • x, ⟨?_, hg⟩, by simp⟩
    change g⁻¹ • g • x ∈ B
    rw [inv_smul_smul]
    exact hx
  have hB' : ∀ g : G, NullMeasurableSet ((fun y => g • y) ⁻¹' B) (μ.restrict D) := fun g =>
    (hB.preimage (measurePreserving_smul g μ).quasiMeasurePreserving).mono
      Measure.restrict_le_self
  calc ∫⁻ x in B, u x ∂μ
      ≤ ∫⁻ x in ⋃ g : G, g • (((fun y => g • y) ⁻¹' B) ∩ D), u x ∂μ :=
        lintegral_mono_set' hcov
    _ ≤ ∑' g : G, ∫⁻ x in g • (((fun y => g • y) ⁻¹' B) ∩ D), u x ∂μ := lintegral_iUnion_le _ _
    _ = ∑' g : G, ∫⁻ x, u x ∂((μ.restrict D).restrict ((fun y => g • y) ⁻¹' B)) := by
        refine tsum_congr fun g => ?_
        rw [Measure.restrict_restrict₀ (hB' g), ← image_smul,
          ← (measurePreserving_smul g μ).setLIntegral_comp_emb (measurableEmbedding_const_smul g)]
        simp only [hu]
    _ = ∫⁻ x, u x ∂(Measure.sum fun g : G =>
          (μ.restrict D).restrict ((fun y => g • y) ⁻¹' B)) := (lintegral_sum_measure _ _).symm
    _ ≤ ∫⁻ x, u x ∂(m • μ.restrict D) :=
        lintegral_mono' (sum_restrict_preimage_smul_le hB hm) le_rfl
    _ = m * ∫⁻ x in D, u x ∂μ := by rw [lintegral_smul_measure, smul_eq_mul]


omit [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] in
@[to_additive ae_encard_vadd_mem_le_one
]
theorem ae_encard_smul_mem_le_one (hD : IsFundamentalDomain G D μ) :
    ∀ᵐ x ∂μ, {g : G | g • x ∈ D}.encard ≤ 1 := by
  have h : ∀ᵐ x ∂μ, ∀ g₁ g₂ : G, g₁ ≠ g₂ → x ∉ g₁ • D ∩ g₂ • D := by
    refine ae_all_iff.2 fun g₁ => ae_all_iff.2 fun g₂ => ?_
    by_cases h : g₁ = g₂
    · simp [h]
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hD.aedisjoint h)] with x hx _ using hx
  filter_upwards [h] with x hx
  rw [encard_le_one_iff]
  intro a b ha hb
  by_contra hab
  refine hx a⁻¹ b⁻¹ (by simpa using hab) ⟨?_, ?_⟩
  · rw [mem_smul_set_iff_inv_smul_mem, inv_inv]; exact ha
  · rw [mem_smul_set_iff_inv_smul_mem, inv_inv]; exact hb

@[to_additive setLIntegral_le_of_isAddFundamentalDomain_of_ae_covers
]
theorem setLIntegral_le_of_isFundamentalDomain_of_ae_covers {D' : Set X}
    (hD : IsFundamentalDomain G D μ) (hD' : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D')
    {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in D, u x ∂μ ≤ ∫⁻ x in D', u x ∂μ := by
  have := setLIntegral_le_mul_of_ae_covers hD' hD.nullMeasurableSet hu (m := 1) (by
    filter_upwards [ae_restrict_of_ae (ae_encard_smul_mem_le_one hD)] with x hx
    exact_mod_cast ENat.toENNReal_le.2 hx)
  simpa using this

@[to_additive measure_le_of_isAddFundamentalDomain_of_ae_covers
]
theorem measure_le_of_isFundamentalDomain_of_ae_covers {D' : Set X}
    (hD : IsFundamentalDomain G D μ) (hD' : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D') : μ D ≤ μ D' := by
  simpa using setLIntegral_le_of_isFundamentalDomain_of_ae_covers hD hD' (u := fun _ => 1)
    (fun _ _ => rfl)

end Multiplicity

section Subgroup

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
  [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G] {D D' : Set X}
  {K : Subgroup G}

variable {E : Type*} [NormedAddCommGroup E]

variable [NormedSpace ℝ E]

end Subgroup

section Kernel

variable {G H X : Type*} [Group G] [Group H] [MulAction G X] [MulAction H X] [MeasurableSpace X]
  {μ : Measure X} {B D D' : Set X} {φ : G →* H}

variable [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G]

variable {K : Subgroup G} {H' : Type*} [Group H'] [MulAction H' X] {φ' : K →* H'}

end Kernel

section Image

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
  [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G] {B D D' : Set X}
  {K : Subgroup G}

end Image

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal
section
open Set Metric Filter Topology
open scoped Nat

namespace GlobalTheory

section Periodic

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem entire_apply_eq_of_isZLattice_periodic [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → V} (hF : Differentiable ℂ F) (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hper : ∀ x, ∀ g ∈ L, F (x + g) = F x) (z w : E) : F z = F w :=
  hF.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L F hF.continuous hper).isBounded z w


omit [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem periodic_of_mem_span_int {F : E → V} {S : Set E}
    (hper : ∀ x, ∀ g ∈ S, F (x + g) = F x) :
    ∀ x, ∀ g ∈ Submodule.span ℤ S, F (x + g) = F x := by
  let P : AddSubgroup E :=
    { carrier := {g | ∀ x, F (x + g) = F x}
      zero_mem' := fun x => by simp
      add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
      neg_mem' := fun {a} ha x => by rw [← ha (x + -a)]; simp }
  intro x g hg
  have : Submodule.span ℤ S ≤ AddSubgroup.toIntSubmodule P :=
    Submodule.span_le.2 fun s hs y => hper y s hs
  exact this hg x

theorem entire_apply_eq_of_periodic_of_span_real [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → V} (hF : Differentiable ℂ F) {S : Set E} (hS : Submodule.span ℝ S = ⊤)
    (hper : ∀ x, ∀ g ∈ S, F (x + g) = F x) (z w : E) : F z = F w := by
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent ℝ S
  let b : Module.Basis t ℝ E := Module.Basis.mk hli (by simp [hspan, hS])
  haveI : Finite t := Module.Finite.finite_basis b
  refine entire_apply_eq_of_isZLattice_periodic hF (Submodule.span ℤ (range b))
    (periodic_of_mem_span_int ?_) z w
  rintro x _ ⟨i, rfl⟩
  exact hper x _ (by simpa [b] using htS i.2)

end Periodic

section Polynomial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem iteratedDeriv_zero_eq_zero_of_poly_bound {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) {n : ℕ} (hn : m < n) :
    iteratedDeriv n F 0 = 0 := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hb 0)
  have key : ∀ R : ℝ, 1 ≤ R → ‖iteratedDeriv n F 0‖ ≤ (n ! * C * 2 ^ m) / R := by
    intro R hR
    have hR0 : 0 < R := by linarith
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) (R := R)
      (C := C * (2 ^ m * R ^ m)) n hR0 hF.diffContOnCl (fun z hz => by
        have hz' : ‖z‖ = R := by simpa using hz
        refine (hb z).trans ?_
        rw [hz', ← mul_pow]
        gcongr
        linarith)
    refine h.trans ?_
    rw [div_le_div_iff₀ (by positivity) hR0]
    have : R ^ m * R ≤ R ^ n := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hR hn
    calc (n ! : ℝ) * (C * (2 ^ m * R ^ m)) * R = (n ! * C * 2 ^ m) * (R ^ m * R) := by ring
      _ ≤ _ := by gcongr
  have lim : Tendsto (fun R : ℝ => (n ! * C * 2 ^ m) / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  exact norm_le_zero_iff.1 (ge_of_tendsto lim ((eventually_ge_atTop 1).mono key))

theorem entire_eq_taylor_sum_of_poly_bound {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) (z : ℂ) :
    F z = ∑ k ∈ Finset.range (m + 1), z ^ k • ((k ! : ℂ)⁻¹ • iteratedDeriv k F 0) := by
  have h := Complex.hasSum_taylorSeries_of_entire hF 0 z
  have h2 := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (f := fun n : ℕ => (n ! : ℂ)⁻¹ • (z - 0) ^ n • iteratedDeriv n F 0)
    (s := Finset.range (m + 1)) (fun n hn => by
      have : m < n := by simpa using hn
      simp [iteratedDeriv_zero_eq_zero_of_poly_bound hF hb this])
  rw [h.unique h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sub_zero, smul_comm]

theorem entire_exists_coeff_of_poly_bound {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ a : ℕ → V, ∀ z, F z = ∑ k ∈ Finset.range (m + 1), z ^ k • a k :=
  ⟨_, entire_eq_taylor_sum_of_poly_bound hF hb⟩

theorem entire_exists_polynomial_of_poly_bound {F : ℂ → ℂ} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ m ∧ ∀ z, F z = p.eval z := by
  obtain ⟨a, ha⟩ := entire_exists_coeff_of_poly_bound hF hb
  refine ⟨∑ k ∈ Finset.range (m + 1), Polynomial.monomial k (a k), ?_, fun z => ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    exact (Polynomial.natDegree_monomial_le _).trans (by simpa [Nat.lt_succ_iff] using hk)
  · rw [ha z, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_comm]

end Polynomial

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsUnitEvalOfMapResidueNeZero
section
open scoped BigOperators
open Module

namespace GlobalTheory

section PolynomialFunction

variable (K : Type*) [CommSemiring K] {M : Type*} [AddCommMonoid M] [Module K M]

variable {K}

end PolynomialFunction

section Frames

variable {ι : Type*} {K : Type*} {V : ι → Type*}

section Semiring

variable [CommSemiring K] [∀ s, AddCommMonoid (V s)] [∀ s, Module K (V s)]
  {l m n : ι → Type*} [∀ s, Fintype (l s)] [∀ s, Fintype (m s)]

abbrev EntryIndex (m n : ι → Type*) : Type _ := Σ s, m s × n s

def entries {α : Type*} (b : ∀ s, Matrix (m s) (n s) α) : EntryIndex m n → α :=
  fun k => b k.1 k.2.1 k.2.2

def ofEntries {α : Type*} (ξ : EntryIndex m n → α) : ∀ s, Matrix (m s) (n s) α :=
  fun s => Matrix.of fun i j => ξ ⟨s, i, j⟩

omit [∀ s, Fintype (m s)] in
@[simp] theorem entries_apply {α : Type*} (b : ∀ s, Matrix (m s) (n s) α) (s : ι) (i : m s)
    (j : n s) : entries b ⟨s, i, j⟩ = b s i j := rfl




end Semiring

variable [Fintype ι] {r : ι → ℕ} [Field K] [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)]
  {W : Type*} [AddCommGroup W] [Module K W]


end Frames

section Hadamard

variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {𝕜 : Type*} [RCLike 𝕜] {V : ι → Type*}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

section Inner

variable [∀ s, NormedAddCommGroup (V s)] [∀ s, InnerProductSpace 𝕜 (V s)]
  [∀ s, FiniteDimensional 𝕜 (V s)]

end Inner

end Hadamard

section PolynomialWeight

variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {K : Type*} [Field K]

noncomputable def detProdPoly (R : Type*) [CommRing R] (n : ι → Type*) [∀ s, Fintype (n s)]
    [∀ s, DecidableEq (n s)] : MvPolynomial (EntryIndex n n) R :=
  ∏ s, (ofEntries MvPolynomial.X s).det

end PolynomialWeight

section HadamardPolynomial

variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {𝕜 : Type*} [RCLike 𝕜]

end HadamardPolynomial

section Gauss

open MvPolynomial IsLocalRing

variable {K Γ O : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ}
  [CommRing O] [Algebra O K]

variable [IsLocalRing O] [Infinite (ResidueField O)]

variable {ι : Type*} [Fintype ι]

section Matrices

variable {n : ι → Type*} [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]

end Matrices

section Lattices

variable {V : ι → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ s, Module O (V s)]
  [∀ s, IsScalarTower O K (V s)] {Λ : ∀ s, Submodule O (V s)}

variable {r : ι → ℕ}

end Lattices

end Gauss

end GlobalTheory
end

