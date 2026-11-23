module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0012

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIntegralFormCovolume
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module MeasureTheory Matrix

noncomputable section

variable (Q V K : Type*) [AddCommGroup Q] [Module ℚ Q] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype K]

theorem IntegralFormCovolume.proof : IntegralFormCovolume.Statement Q V K := by
  classical
  intro ψ e T μ hμ hT hli hrank
  have : FiniteDimensional ℚ Q := Module.Finite.of_basis e
  have hQ : finrank ℚ Q = Fintype.card K := finrank_eq_card_basis e
  let b₀ : Basis K ℝ V := basisOfLinearIndependentOfCardEqFinrank' _ hli hrank.symm
  have hb₀ : ∀ i, b₀ i = ψ (e i) := fun i => by simp [b₀]
  have hGe : (LinearMap.BilinForm.toMatrix e T).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero e).1 hT
  refine ⟨μ.real (ZSpan.fundamentalDomain b₀) ^ 2 /
    |((LinearMap.BilinForm.toMatrix e T).det : ℝ)|, ?_⟩
  intro L k hk hfg hspan _ hdual
  set M := AddSubgroup.toIntSubmodule L with hM
  have : Module.Finite ℤ M := Module.Finite.iff_fg.2 ((Submodule.fg_iff_addSubgroup_fg M).2 hfg)
  have : Module.IsTorsionFree ℤ Q := .trans_faithfulSMul ℤ ℚ Q
  have hψq : ∀ (q : ℚ) (y : Q), ψ (q • y) = (q : ℝ) • ψ y := fun q y => by
    simpa using map_ratCast_smul ψ ℚ ℝ q y

  let x₀ := Module.Free.chooseBasis ℤ M
  have hli₀ : LinearIndependent ℚ (M.subtype ∘ x₀) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).1
      (x₀.linearIndependent.map' M.subtype (Submodule.ker_subtype M))
  have hspan₀ : Submodule.span ℤ (Set.range (M.subtype ∘ x₀)) = M := by
    rw [Set.range_comp, Submodule.span_image, x₀.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspanq : Submodule.span ℚ (Set.range (M.subtype ∘ x₀)) = ⊤ := by
    rw [← Submodule.span_span_of_tower ℤ, hspan₀]
    exact hspan
  let xq₀ : Basis _ ℚ Q := Basis.mk hli₀ hspanq.ge
  let σ := Fintype.equivOfCardEq ((finrank_eq_card_basis xq₀).symm.trans hQ)
  let x := x₀.reindex σ
  let xq := xq₀.reindex σ
  have hxq : ∀ i, xq i = (x i : Q) := fun i => by simp [xq, x, xq₀]
  have hspanx : Submodule.span ℤ (Set.range fun i => xq i) = M := by
    have : (fun i => xq i) = M.subtype ∘ x := funext hxq
    rw [this, Set.range_comp, Submodule.span_image, x.span_eq, Submodule.map_top,
      Submodule.range_subtype]

  set P := e.toMatrix xq with hP
  have hψe : ∀ y, ψ y = ∑ i, (e.repr y i : ℝ) • b₀ i := fun y => by
    calc ψ y = ψ (∑ i, e.repr y i • e i) := by rw [e.sum_repr]
      _ = _ := by rw [map_sum]; simp only [hψq, hb₀]
  have hmat : b₀.toMatrix (fun j => ψ (xq j)) = P.map (Rat.cast : ℚ → ℝ) := by
    ext i j
    rw [Basis.toMatrix_apply, hψe, b₀.repr_sum_self]
    simp [P, Basis.toMatrix_apply]
  have hdetP : b₀.det (fun j => ψ (xq j)) = (P.det : ℝ) := by
    rw [Basis.det_apply, hmat]
    simpa using (RingHom.map_det (Rat.castHom ℝ) P).symm
  have hP0 : P.det ≠ 0 := by
    rw [hP, ← Basis.det_apply]
    exact (e.isUnit_det xq).ne_zero
  have hw : LinearIndependent ℝ (fun j => ψ (xq j)) :=
    ((Basis.is_basis_iff_det b₀).2 (by rw [hdetP]; exact isUnit_iff_ne_zero.2 (by exact_mod_cast hP0))).1
  let bx : Basis K ℝ V := basisOfLinearIndependentOfCardEqFinrank' _ hw hrank.symm
  have hL : AddSubgroup.toIntSubmodule (L.map ψ) = Submodule.span ℤ (Set.range bx) := by
    change M.map ψ.toIntLinearMap = _
    rw [← hspanx, Submodule.map_span, ← Set.range_comp]
    congr 1
    simp [bx, Function.comp_def]

  have hPk : P.det ^ 2 * |(LinearMap.BilinForm.toMatrix e T).det| ≤ |(k : ℚ)| ^ Fintype.card K := by
    have hG : (LinearMap.BilinForm.toMatrix xq T).det =
        P.det ^ 2 * (LinearMap.BilinForm.toMatrix e T).det := by
      rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix e xq T, det_mul, det_mul, det_transpose]
      ring
    set d := T.dualBasis hT xq
    have hd : ∀ i j, T (d i) (xq j) = if j = i then 1 else 0 :=
      LinearMap.BilinForm.apply_dualBasis_left hT xq
    have hc : ∀ i, ∃ c : K → ℤ, ∑ j, c j • xq j = k • d i := by
      intro i
      have hmem : k • d i ∈ L := hdual (d i) fun y hy => by
        have hy' : y ∈ Submodule.span ℤ (Set.range fun j => xq j) := by rw [hspanx]; exact hy
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
        exact ⟨c i, by simp [map_sum, hd]⟩
      have hmem' : k • d i ∈ Submodule.span ℤ (Set.range fun j => xq j) := by
        rw [hspanx]; exact hmem
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).1 hmem'
    choose c₀ hc using hc
    set c : Matrix K K ℤ := Matrix.of c₀ with hcdef
    have hcG : c.map (Int.cast : ℤ → ℚ) * LinearMap.BilinForm.toMatrix xq T = (k : ℚ) • 1 := by
      ext i l
      have h1 := congrArg (fun y => T y (xq l)) (hc i)
      simp [hd] at h1
      rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
      simp only [Matrix.map_apply, LinearMap.BilinForm.toMatrix_apply, hcdef, Matrix.of_apply]
      simpa [zsmul_eq_mul, eq_comm] using h1
    have hdet := congrArg Matrix.det hcG
    rw [det_mul, det_smul, det_one, mul_one, hG] at hdet
    have hcd : (c.map (Int.cast : ℤ → ℚ)).det = (c.det : ℚ) := by
      simpa using (RingHom.map_det (Int.castRingHom ℚ) c).symm
    rw [hcd] at hdet
    have hc0 : c.det ≠ 0 := by
      rintro h0
      rw [h0, Int.cast_zero, zero_mul] at hdet
      exact pow_ne_zero _ (Int.cast_ne_zero.2 hk) hdet.symm
    have h1 : (1 : ℚ) ≤ |(c.det : ℚ)| := by exact_mod_cast Int.one_le_abs hc0
    calc P.det ^ 2 * |(LinearMap.BilinForm.toMatrix e T).det|
        = |P.det ^ 2 * (LinearMap.BilinForm.toMatrix e T).det| := by
          rw [abs_mul, abs_pow, sq_abs]
      _ ≤ |(c.det : ℚ)| * |P.det ^ 2 * (LinearMap.BilinForm.toMatrix e T).det| :=
          le_mul_of_one_le_left (abs_nonneg _) h1
      _ = |(k : ℚ)| ^ Fintype.card K := by rw [← abs_mul, hdet, abs_pow]
  have hPkR : (P.det : ℝ) ^ 2 * |((LinearMap.BilinForm.toMatrix e T).det : ℝ)| ≤
      |(k : ℝ)| ^ Fintype.card K := by exact_mod_cast hPk

  rw [hL]
  refine ⟨inferInstance, inferInstance, ?_⟩
  have := hμ
  let bZ : Basis K ℤ (Submodule.span ℤ (Set.range bx)) :=
    Basis.span (bx.linearIndependent.restrict_scalars' ℤ)
  have hcoe : ((↑) ∘ bZ : K → V) = fun j => ψ (xq j) := funext fun i => by
    simp [bZ, Basis.span_apply, bx]
  rw [ZLattice.covolume_eq_det_mul_measureReal _ μ bZ b₀, hcoe, hdetP, mul_pow, sq_abs,
    div_mul_eq_mul_div, le_div_iff₀ (abs_pos.2 (by exact_mod_cast hGe))]
  calc (P.det : ℝ) ^ 2 * μ.real (ZSpan.fundamentalDomain b₀) ^ 2 *
        |((LinearMap.BilinForm.toMatrix e T).det : ℝ)|
      = μ.real (ZSpan.fundamentalDomain b₀) ^ 2 *
        ((P.det : ℝ) ^ 2 * |((LinearMap.BilinForm.toMatrix e T).det : ℝ)|) := by ring
    _ ≤ μ.real (ZSpan.fundamentalDomain b₀) ^ 2 * |(k : ℝ)| ^ Fintype.card K :=
        mul_le_mul_of_nonneg_left hPkR (sq_nonneg _)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTorusIntegralHomogeneous
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {κ : Type*} [Fintype κ]

private lemma weighted_sum_smul (q : κ → ℝ) (t : ℝ) (b : κ → ℂ) :
    ∑ i, q i * ‖(t • b) i‖ ^ 2 = t ^ 2 * ∑ i, q i * ‖b i‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

private lemma prod_smul (n : ℕ) {t : ℝ} (ht : 0 < t) (b : κ → ℂ) :
    ∏ i, ‖(t • b) i‖ₑ ^ (2 * n) =
      ENNReal.ofReal (t ^ (2 * n * Fintype.card κ)) * ∏ i, ‖b i‖ₑ ^ (2 * n) := by
  simp_rw [Pi.smul_apply, enorm_smul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul,
    Real.enorm_eq_ofReal ht.le, ENNReal.ofReal_pow ht.le]

private lemma indicator_smul (q : κ → ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) (b : κ → ℂ) :
    {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < t ^ 2}.indicator
        (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) (t • b) =
      ENNReal.ofReal (t ^ (2 * n * Fintype.card κ)) *
        {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
          (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b := by
  have hmem : (t • b) ∈ {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < t ^ 2} ↔
      b ∈ {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2} := by
    simp only [Set.mem_ofPred_eq, weighted_sum_smul, one_pow]
    exact mul_lt_iff_lt_one_right (by positivity)
  by_cases hb : b ∈ {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}
  · rw [Set.indicator_of_mem (hmem.2 hb), Set.indicator_of_mem hb, prod_smul n ht]
  · rw [Set.indicator_of_notMem (fun h => hb (hmem.1 h)), Set.indicator_of_notMem hb, mul_zero]

private lemma measurable_integrand (q : κ → ℝ) (n : ℕ) (s : ℝ) :
    Measurable ({b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < s}.indicator
      (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n))) := by
  refine Measurable.indicator ?_ ?_
  · exact Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).enorm.pow_const _
  · exact measurableSet_lt (Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((measurable_pi_apply i).norm.pow_const 2)) measurable_const

private lemma finrank_fun_complex : Module.finrank ℝ (κ → ℂ) = 2 * Fintype.card κ := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, smul_eq_mul,
    Finset.card_univ, mul_comm]

private lemma integral_scaling (q : κ → ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫⁻ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < t ^ 2}.indicator
        (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b =
      (∫⁻ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
        (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b) *
        ENNReal.ofReal (t ^ ((2 * n + 2) * Fintype.card κ)) := by
  set g : (κ → ℂ) → ℝ≥0∞ := {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
    (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) with hg
  have hpt : ∀ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < t ^ 2}.indicator
      (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b =
        ENNReal.ofReal (t ^ (2 * n * Fintype.card κ)) * g (t⁻¹ • b) := by
    intro b
    have h := indicator_smul q n ht (t⁻¹ • b)
    rwa [smul_inv_smul₀ ht.ne'] at h
  have hmeas : Measurable g := measurable_integrand q n _
  have hmap : ∫⁻ b : κ → ℂ, g (t⁻¹ • b) =
      ENNReal.ofReal (t ^ (2 * Fintype.card κ)) * ∫⁻ b, g b := by
    rw [← lintegral_map hmeas (measurable_const_smul _),
      Measure.map_addHaar_smul volume (inv_ne_zero ht.ne'), lintegral_smul_measure,
      finrank_fun_complex, inv_pow, inv_inv, abs_of_pos (by positivity : 0 < t ^ (2 * Fintype.card κ)),
      smul_eq_mul]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmap, ← mul_assoc,
    mul_comm, ← ENNReal.ofReal_mul (by positivity), ← pow_add]
  congr 3
  ring

theorem TorusIntegralHomogeneous.proof (κ : Type*) [Fintype κ] :
    TorusIntegralHomogeneous.Statement κ := by
  intro q hq n
  refine ⟨∫⁻ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
      (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b, ?_, ?_, fun t ht => integral_scaling q n ht⟩
  ·
    rw [lintegral_pos_iff_support (measurable_integrand q n _)]
    have hS : 0 ≤ ∑ i, q i := Finset.sum_nonneg fun i _ => (hq i).le
    let V : Set (κ → ℂ) :=
      {b | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2} ∩ ⋂ i, {b | b i ≠ 0}
    have hVo : IsOpen V :=
      (isOpen_lt (by fun_prop) continuous_const).inter
        (isOpen_iInter_of_finite fun i => isOpen_ne_fun (continuous_apply i) continuous_const)
    have hVne : V.Nonempty := by
      have hx : 0 < ((∑ i, q i) + 1)⁻¹ := by positivity
      have h1 : ‖((((∑ i, q i) + 1)⁻¹ : ℝ) : ℂ)‖ = ((∑ i, q i) + 1)⁻¹ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hx.le]
      refine ⟨fun _ => ((((∑ i, q i) + 1)⁻¹ : ℝ) : ℂ), ?_, ?_⟩
      · show ∑ i, q i * ‖((((∑ i, q i) + 1)⁻¹ : ℝ) : ℂ)‖ ^ 2 < 1 ^ 2
        rw [h1, ← Finset.sum_mul, one_pow, inv_pow, ← div_eq_mul_inv,
          div_lt_one (by positivity)]
        nlinarith
      · exact Set.mem_iInter.2 fun i => Complex.ofReal_ne_zero.2 hx.ne'
    refine lt_of_lt_of_le (hVo.measure_pos volume hVne) (measure_mono ?_)
    rintro b ⟨hb1, hb2⟩
    rw [Function.mem_support, Set.indicator_of_mem hb1]
    exact Finset.prod_ne_zero_iff.2 fun i _ =>
      pow_ne_zero _ (enorm_ne_zero.2 (Set.mem_iInter.1 hb2 i))
  ·
    set R : ℝ := ∑ i, (q i)⁻¹ + 1 with hR
    have hR1 : 1 ≤ R := by
      have : 0 ≤ ∑ i, (q i)⁻¹ := Finset.sum_nonneg fun i _ => (inv_pos.2 (hq i)).le
      linarith
    have hbd : ∀ b ∈ {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}, ∀ i, ‖b i‖ < R := by
      intro b hb i
      have hb' : ∑ j, q j * ‖b j‖ ^ 2 < 1 := by simpa using hb
      have hi : q i * ‖b i‖ ^ 2 < 1 :=
        lt_of_le_of_lt (Finset.single_le_sum (f := fun j => q j * ‖b j‖ ^ 2)
          (fun j _ => mul_nonneg (hq j).le (sq_nonneg _)) (Finset.mem_univ i)) hb'
      have hsq : ‖b i‖ ^ 2 < (q i)⁻¹ := by
        calc ‖b i‖ ^ 2 = (q i)⁻¹ * (q i * ‖b i‖ ^ 2) := by
              rw [← mul_assoc, inv_mul_cancel₀ (hq i).ne', one_mul]
          _ < (q i)⁻¹ * 1 := mul_lt_mul_of_pos_left hi (inv_pos.2 (hq i))
          _ = (q i)⁻¹ := mul_one _
      have hle : (q i)⁻¹ ≤ ∑ j, (q j)⁻¹ :=
        Finset.single_le_sum (f := fun j => (q j)⁻¹) (fun j _ => (inv_pos.2 (hq j)).le)
          (Finset.mem_univ i)
      have hx := norm_nonneg (b i)
      by_contra! h
      nlinarith
    have hsub : {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2} ⊆ Metric.ball 0 R := by
      intro b hb
      rw [mem_ball_zero_iff, pi_norm_lt_iff (by linarith)]
      exact hbd b hb
    have hle : {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
          (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) ≤
        {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
          (fun _ => ∏ _i : κ, ENNReal.ofReal R ^ (2 * n)) := by
      intro b
      by_cases hb : b ∈ {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}
      · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb]
        refine Finset.prod_le_prod' fun i _ => pow_le_pow_left' ?_ _
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hbd b hb i).le
      · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb]
    calc _ ≤ ∫⁻ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2}.indicator
          (fun _ => ∏ _i : κ, ENNReal.ofReal R ^ (2 * n)) b := lintegral_mono hle
      _ ≤ (∏ _i : κ, ENNReal.ofReal R ^ (2 * n)) *
          volume {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < 1 ^ 2} := lintegral_indicator_const_le _ _
      _ < ⊤ := ENNReal.mul_lt_top
          (ENNReal.prod_lt_top fun i _ => ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          (lt_of_le_of_lt (measure_mono hsub) measure_ball_lt_top)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusHaar
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory Module

theorem det_sq_eq_one_of_preserves_bilin {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (f : V →ₗ[ℝ] V) (hf : ∀ x y, B (f x) (f y) = B x y) : LinearMap.det f ^ 2 = 1 :=
  _root_.UpperTheory.Reformulated.B.Qm9.det_sq_eq_one_of_preserves_bilin B hB f hf

theorem measurePreserving_of_preserves_bilin {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (f : V →ₗ[ℝ] V) (hf : ∀ x y, B (f x) (f y) = B x y) : MeasurePreserving f μ μ := by
  have h2 := det_sq_eq_one_of_preserves_bilin B hB f hf
  have hd : LinearMap.det f ≠ 0 := by
    intro h
    rw [h] at h2
    norm_num at h2
  have habs : |LinearMap.det f| = 1 := by
    have : |LinearMap.det f| ^ 2 = 1 := by rw [sq_abs]; exact h2
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).1 this
  refine ⟨(LinearMap.continuous_of_finiteDimensional f).measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ hd, abs_inv, habs]
  simp

theorem map_eq_of_measurePreserving_coordinates {N V : Type*} [Group N] [TopologicalSpace N]
    [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [MeasurableSpace N]
    [BorelSpace N] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] (lam : Measure V)
    [IsFiniteMeasureOnCompacts lam] [lam.IsOpenPosMeasure] (φ : V ≃ₜ N)
    (hL : ∀ n : N, MeasurePreserving (fun x => φ.symm (n * φ x)) lam lam)
    (c : N → N) (hC : MeasurePreserving (fun x => φ.symm (c (φ x))) lam lam)
    (μ : Measure N) [μ.IsHaarMeasure] : μ.map c = μ := by
  have hφ : Measurable φ := φ.continuous.measurable
  have key : ∀ T : V → V, MeasurePreserving T lam lam →
      (lam.map φ).map (φ ∘ T ∘ φ.symm) = lam.map φ := by
    intro T hT
    rw [Measure.map_map (hφ.comp (hT.measurable.comp φ.symm.continuous.measurable)) hφ]
    have : (φ ∘ T ∘ φ.symm) ∘ φ = φ ∘ T := by
      funext x
      simp
    rw [this, ← Measure.map_map hφ hT.measurable, hT.map_eq]
  have hinv : (lam.map φ).IsMulLeftInvariant := by
    refine ⟨fun n => ?_⟩
    have e : (fun x => n * x) = φ ∘ (fun x => φ.symm (n * φ x)) ∘ φ.symm := by
      funext x
      simp
    rw [e]
    exact key _ (hL n)
  have : IsFiniteMeasureOnCompacts (lam.map φ) := by
    refine ⟨fun K hK => ?_⟩
    have e := φ.toMeasurableEquiv.map_apply (μ := lam) K
    simp only [Homeomorph.toMeasurableEquiv_coe] at e
    rw [e]
    exact (φ.isCompact_preimage.2 hK).measure_lt_top
  have : (lam.map φ).IsOpenPosMeasure := φ.continuous.isOpenPosMeasure_map φ.surjective
  have : (lam.map φ).IsHaarMeasure := {}
  have e : c = φ ∘ (fun x => φ.symm (c (φ x))) ∘ φ.symm := by
    funext x
    simp
  have hc : AEMeasurable c (lam.map φ) := by
    rw [φ.measurableEmbedding.aemeasurable_map_iff]
    simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using
      (hφ.comp hC.measurable).aemeasurable (μ := lam)
  rw [Measure.isMulLeftInvariant_eq_smul μ (lam.map φ), Measure.map_smul _ hc]
  congr 1
  rw [e]
  exact key _ hC

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

