module

public import Mathlib
public import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
public import ReciprocityTheory.ThetaQuasiPeriods.Transl
public import ReciprocityTheory.ThetaQuasiPeriods.Change
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.AdditionLevelTwoMul
section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.ThetaAddition

theorem exists_sum_mul {X Y : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V]
    (L : Submodule ℂ (Y → ℂ)) (F : X → Y → ℂ) (h1 : ∀ y, (fun x => F x y) ∈ V)
    (h2 : ∀ x, F x ∈ L) :
    ∃ (n : ℕ) (h : Fin n → X → ℂ) (k : Fin n → Y → ℂ), (∀ i, h i ∈ V ∧ k i ∈ L) ∧
      ∀ x y, F x y = ∑ i, h i x * k i y := by
  first
  | exact @_root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul
  | exact _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul
  | (apply _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul ..)

theorem left_mem {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) {f f' : (Fin g → ℂ) → ℂ}
    (hf : f ∈ thetaLevel N τ) (hf' : f' ∈ thetaLevel N τ) (w : Fin g → ℂ) :
    (fun z => f (z + w) * f' (z - w)) ∈ thetaLevel (2 * N) τ := by
  refine ⟨(hf.1.comp (by fun_prop)).mul (hf'.1.comp (by fun_prop)), fun n n' z => ?_⟩
  have e1 : z + τ *ᵥ ofIntVec n + ofIntVec n' + w = (z + w) + τ *ᵥ ofIntVec n + ofIntVec n' := by
    abel
  have e2 : z + τ *ᵥ ofIntVec n + ofIntVec n' - w = (z - w) + τ *ᵥ ofIntVec n + ofIntVec n' := by
    abel
  show f _ * f' _ = _ * (f _ * f' _)
  rw [e1, e2, hf.2, hf'.2, mul_mul_mul_comm, ← eC_add]
  congr 2
  rw [dotProduct_add, dotProduct_sub]; push_cast; ring

theorem right_mem {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) {f f' : (Fin g → ℂ) → ℂ}
    (hf : f ∈ thetaLevel N τ) (hf' : f' ∈ thetaLevel N τ) (z : Fin g → ℂ) :
    (fun w => f (z + w) * f' (z - w)) ∈ thetaLevel (2 * N) τ := by
  refine ⟨(hf.1.comp (by fun_prop)).mul (hf'.1.comp (by fun_prop)), fun n n' w => ?_⟩
  have e1 : z + (w + τ *ᵥ ofIntVec n + ofIntVec n') = (z + w) + τ *ᵥ ofIntVec n + ofIntVec n' := by
    abel
  have e2 : z - (w + τ *ᵥ ofIntVec n + ofIntVec n')
      = (z - w) + τ *ᵥ ofIntVec (-n) + ofIntVec (-n') := by
    rw [ofIntVec_neg, ofIntVec_neg, mulVec_neg]; abel
  show f _ * f' _ = _ * (f _ * f' _)
  rw [e1, e2, hf.2, hf'.2, mul_mul_mul_comm, ← eC_add]
  congr 2
  rw [ofIntVec_neg, mulVec_neg, neg_dotProduct_neg, neg_dotProduct, dotProduct_add, dotProduct_sub]
  push_cast; ring

theorem addition_level_two_mul :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f f' : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → (Differentiable ℂ f' ∧ ∀ (n n' : Fin g → ℤ) z, f' (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f' z) → ∃ (n : ℕ) (h k : Fin n → (Fin g → ℂ) → ℂ), (∀ i, (Differentiable ℂ (h i) ∧ ∀ (n n' : Fin g → ℤ) z, (h i) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((2 * N : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (h i) z) ∧ (Differentiable ℂ (k i) ∧ ∀ (n n' : Fin g → ℤ) z, (k i) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((2 * N : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (k i) z)) ∧ ∀ z w, f (z + w) * f' (z - w) = ∑ i, h i z * k i w) := by
  intro H1 H2 g τ hτ N hN f f' hf hf'
  have hN2 : 1 ≤ 2 * N := by omega
  have hle : thetaLevel (2 * N) τ ≤ _ := fun φ hφ => H2 g τ hτ (2 * N) hN2 φ hφ
  haveI : FiniteDimensional ℂ (thetaLevel (2 * N) τ) := by
    haveI := FiniteDimensional.span_of_finite ℂ (Set.finite_range
      (fun (c : Fin g → Fin (2 * N)) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / (2 * N : ℕ)) 0 (((2 * N : ℕ) : ℂ) • z) (((2 * N : ℕ) : ℂ) • τ)))
    exact Submodule.finiteDimensional_of_le hle
  exact exists_sum_mul (thetaLevel (2 * N) τ) (thetaLevel (2 * N) τ)
    (fun z w => f (z + w) * f' (z - w)) (left_mem τ N hf hf') (right_mem τ N hf hf')

end GlobalTheory.ThetaAddition
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ClassicalThetaLevelAndLinearIndependent
section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

theorem classicalTheta_level_and_linearIndependent' (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ)
    (hτ : τ ∈ SiegelH (Fin g)) (N : ℕ) (hN : 1 ≤ N) :
    (∀ c : Fin g → Fin N,
      (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧
        ∀ (n n' : Fin g → ℤ) z,
          (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))
              (z + τ *ᵥ ofIntVec n + ofIntVec n') =
            eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) *
              (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧
    LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
      theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) := by
  have e (c : Fin g → Fin N) : levelTheta 0 0 N τ (fun i => ((c i : ℕ) : ℤ)) =
      fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) := by
    funext z
    rw [levelTheta_zero_zero]
    simp only [Int.cast_natCast]
  refine ⟨fun c => ?_, ?_⟩
  · have h := levelTheta_zero_zero_mem hτ hN (fun i => ((c i : ℕ) : ℤ))
    rw [e] at h
    exact mem_thetaLevel.1 h
  · have h := linearIndependent_levelTheta (a := 0) (b := 0) hτ hN
      (r := fun (c : Fin g → Fin N) i => ((c i : ℕ) : ℤ)) (bijective_fin_zmod hN).1
    simpa only [e] using h


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
theorem _root_.GlobalTheory.classicalTheta_level_and_linearIndependent :
    _root_.ReciprocityTheory.PTheta.SiegelSubDomainStatement → _root_.ReciprocityTheory.PTheta.ThetaHoloStatement → _root_.ReciprocityTheory.PTheta.ThetaMTestStatement → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) := by
  intro _ _ _ g τ hτ N hN
  have hN0 : 0 < N := hN
  have heq : ∀ c : Fin g → Fin N, (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) =
      _root_.GlobalTheory.levelTheta 0 0 N τ (fun i => ((c i : ℕ) : ℤ)) := by
    intro c
    funext z
    rw [_root_.GlobalTheory.levelTheta_zero_zero]
    simp
  refine ⟨fun c => ?_, ?_⟩
  · rw [heq c]
    exact _root_.GlobalTheory.mem_thetaLevel.1 (_root_.GlobalTheory.levelTheta_zero_zero_mem hτ hN0 _)
  · have := _root_.GlobalTheory.linearIndependent_levelTheta (a := 0) (b := 0) hτ hN0
      (r := fun (c : Fin g → Fin N) i => ((c i : ℕ) : ℤ))
      (_root_.GlobalTheory.bijective_fin_zmod (ι := Fin g) hN0).injective
    convert this using 1
    funext c
    exact heq c

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsApplySubSmulNeZeroAndApplyAddNeZero
section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
private lemma dense_setOf_ne_zero_of_differentiable_ne_zero {g : ℕ} {h : (Fin g → ℂ) → ℂ}
    (hd : Differentiable ℂ h) (hne : h ≠ 0) : Dense {u | h u ≠ 0} := by
  have hc : {u | h u ≠ 0} = {u | h u = 0}ᶜ := by
    ext u
    simp
  rw [hc, ← interior_eq_empty_iff_dense_compl, Set.eq_empty_iff_forall_notMem]
  intro x hx
  apply hne
  have hev : ∀ᶠ w in 𝓝 x, h w = 0 := mem_interior_iff_mem_nhds.1 hx
  funext y
  have ht : Filter.Tendsto (fun t : ℂ => x + t • (y - x)) (𝓝 0) (𝓝 x) := by
    have hcont : Continuous (fun t : ℂ => x + t • (y - x)) := by fun_prop
    simpa using hcont.tendsto 0
  have hφd : Differentiable ℂ (fun t : ℂ => h (x + t • (y - x))) :=
    hd.comp ((differentiable_id.smul_const (y - x)).const_add x)
  have hφ0 : (fun t : ℂ => h (x + t • (y - x))) =ᶠ[𝓝 0] 0 := ht.eventually hev
  have hφa : AnalyticOnNhd ℂ (fun t : ℂ => h (x + t • (y - x))) Set.univ :=
    fun t _ => hφd.analyticAt t
  have := hφa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ 0) hφ0 (Set.mem_univ 1)
  simpa using this


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
theorem _root_.GlobalTheory.exists_level_apply_ne_zero_of_two_le :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → (Differentiable ℂ (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) z) ∧ (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) ≠ 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → ∀ N : ℕ, 2 ≤ N → ∀ z, ∃ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * f z) ∧ f z ≠ 0) := by
  intro H g τ hτ N hN z
  obtain ⟨⟨hd, hq⟩, hne⟩ := H g τ hτ
  have hq' : ∀ (n n' : Fin g → ℤ) v, _root_.ReciprocityTheory.PTheta.theta 0 0 (v + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') τ =
      _root_.ReciprocityTheory.PTheta.eC (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ v)) * _root_.ReciprocityTheory.PTheta.theta 0 0 v τ :=
    fun n n' v => hq n n' v
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hM : (M : ℂ) ≠ 0 := by
    have : M ≠ 0 := by omega
    exact_mod_cast this
  have hd1 : Differentiable ℂ (fun u => _root_.ReciprocityTheory.PTheta.theta 0 0 (z + u) τ) := hd.comp (differentiable_id.const_add z)
  have hd2 : Differentiable ℂ (fun u => _root_.ReciprocityTheory.PTheta.theta 0 0 (z - (M : ℂ) • u) τ) :=
    hd.comp ((differentiable_id.const_smul (M : ℂ)).const_sub z)
  have hne1 : (fun u => _root_.ReciprocityTheory.PTheta.theta 0 0 (z + u) τ) ≠ 0 := by
    intro h0
    apply hne
    funext w
    have := congr_fun h0 (w - z)
    simpa using this
  have hne2 : (fun u => _root_.ReciprocityTheory.PTheta.theta 0 0 (z - (M : ℂ) • u) τ) ≠ 0 := by
    intro h0
    apply hne
    funext w
    have := congr_fun h0 (-(M : ℂ)⁻¹ • (w - z))
    simp only [smul_neg, smul_smul, mul_inv_cancel₀ hM, one_smul, sub_neg_eq_add,
      add_sub_cancel, Pi.zero_apply] at this
    simpa [mul_inv_cancel₀ hM] using this
  have hopen : IsOpen {u | _root_.ReciprocityTheory.PTheta.theta 0 0 (z + u) τ ≠ 0} :=
    isOpen_ne_fun hd1.continuous continuous_const
  obtain ⟨u, hu1, hu2⟩ := ((dense_setOf_ne_zero_of_differentiable_ne_zero hd1 hne1).inter_of_isOpen_left
    (dense_setOf_ne_zero_of_differentiable_ne_zero hd2 hne2) hopen).nonempty
  refine ⟨fun w => _root_.ReciprocityTheory.PTheta.theta 0 0 (w + u) τ ^ M * _root_.ReciprocityTheory.PTheta.theta 0 0 (w - (M : ℂ) • u) τ, ⟨?_, ?_⟩, ?_⟩
  · exact ((hd.comp (differentiable_id.add_const u)).pow M).mul
      (hd.comp (differentiable_id.sub_const _))
  · intro n n' w
    have e1 : w + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n' + u = (w + u) + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n' := by abel
    have e2 : w + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n' - (M : ℂ) • u =
        (w - (M : ℂ) • u) + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n' := by abel
    simp only
    rw [e1, e2, hq' n n' (w + u), hq' n n' (w - (M : ℂ) • u), mul_pow, ← _root_.GlobalTheory.eC_nat_mul]
    have key : _root_.ReciprocityTheory.PTheta.eC ((M : ℂ) * (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (w + u)))) *
        _root_.ReciprocityTheory.PTheta.eC (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (w - (M : ℂ) • u))) =
        _root_.ReciprocityTheory.PTheta.eC (-((M + 1 : ℕ) : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ w)) := by
      rw [← _root_.ReciprocityTheory.PTheta.eC_add]
      congr 1
      simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      push_cast
      ring
    rw [← key]
    ring
  · exact mul_ne_zero (pow_ne_zero _ hu1) hu2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanThetaOfLevel
section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.ThetaSpan

theorem ofIntVec_single {g : ℕ} (j : Fin g) :
    ofIntVec (Pi.single j (1 : ℤ)) = (Pi.single j 1 : Fin g → ℂ) := by
  funext i
  by_cases h : i = j
  · subst h; simp [ofIntVec]
  · simp [ofIntVec, Pi.single_eq_of_ne h]

theorem laws_of_level {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) (f : (Fin g → ℂ) → ℂ)
    (h : ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') =
      eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) :
    (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) ∧
      ∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) =
        eC (-(τ j j) / 2) ^ N * cexp (-(2 * Real.pi * I) * N * z j) * f z := by
  refine ⟨fun i z => ?_, fun j z => ?_⟩
  · have := h 0 (Pi.single i 1) z
    rw [ofIntVec_zero, ofIntVec_single] at this
    simpa [eC] using this
  · have := h (Pi.single j 1) 0 z
    rw [ofIntVec_zero, ofIntVec_single, add_zero] at this
    rw [this]
    congr 1
    simp only [eC, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [single_one_dotProduct, mulVec_single_one, Matrix.col_apply, transpose_apply]
    ring


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
theorem _root_.GlobalTheory.ThetaSpan.mem_span_theta_of_level :
  (∀ (g n : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (b : Fin g → ℂ), 1 ≤ n → (∀ j, b j ≠ 0) → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, (Differentiable ℂ (f k) ∧ (∀ (i : Fin g) z, (f k) (z + Pi.single i 1) = (f k) z) ∧ ∀ (j : Fin g) z, (f k) (z + τ.mulVec (Pi.single j 1)) = b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * (f k) z)) → LinearIndependent ℂ f → N ≤ n ^ g) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)))) := by
  intro _ H g τ hτ N hN f hf
  have hN0 : 0 < N := hN
  obtain ⟨hmem, hli⟩ := H g τ hτ N hN
  have hV : _root_.GlobalTheory.thetaLevel N τ = _root_.GlobalTheory.thetaLevelChar 0 0 N τ := by
    ext φ
    simp [_root_.GlobalTheory.mem_thetaLevel, _root_.GlobalTheory.mem_thetaLevelChar, _root_.ReciprocityTheory.PTheta.eC_zero]
  have hsymm : τ.IsSymm := (_root_.GlobalTheory.isSiegel_iff_mem_siegelH.2 hτ).isSymm
  haveI : FiniteDimensional ℂ (_root_.GlobalTheory.thetaLevel N τ) := by
    rw [hV]
    exact _root_.GlobalTheory.finiteDimensional_thetaLevelChar hsymm hN0
  have hrank : Module.finrank ℂ (_root_.GlobalTheory.thetaLevel N τ) = N ^ g := by
    rw [hV, _root_.GlobalTheory.finrank_thetaLevelChar hτ hN0, Fintype.card_fin]
  let v : (Fin g → Fin N) → _root_.GlobalTheory.thetaLevel N τ := fun c => ⟨_, _root_.GlobalTheory.mem_thetaLevel.2 (hmem c)⟩
  have hvli : LinearIndependent ℂ v := LinearIndependent.of_comp (_root_.GlobalTheory.thetaLevel N τ).subtype hli
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ :=
    hvli.span_eq_top_of_card_eq_finrank' (by simp [hrank])
  have hfv : (⟨f, _root_.GlobalTheory.mem_thetaLevel.2 hf⟩ : _root_.GlobalTheory.thetaLevel N τ) ∈ Submodule.span ℂ (Set.range v) := by
    rw [hspan]
    exact Submodule.mem_top
  have := Submodule.mem_map_of_mem (f := (_root_.GlobalTheory.thetaLevel N τ).subtype) hfv
  rw [Submodule.map_span, ← Set.range_comp] at this
  exact this

end GlobalTheory.ThetaSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannThetaLevelOneNeZero
section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
theorem _root_.GlobalTheory.riemannTheta_level_one_ne_zero :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → (Differentiable ℂ (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) z) ∧ (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) ≠ 0) := by
  intro H g τ hτ
  obtain ⟨hd, hq⟩ := (H g τ hτ 1 le_rfl).1 0
  have e : ∀ z, _root_.ReciprocityTheory.PTheta.theta (fun i => (((0 : Fin g → Fin 1) i : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) 0
      (((1 : ℕ) : ℂ) • z) (((1 : ℕ) : ℂ) • τ) = _root_.ReciprocityTheory.PTheta.theta 0 0 z τ := by
    intro z
    simp only [Pi.zero_apply, Fin.val_zero, Nat.cast_zero, zero_div, Nat.cast_one, one_smul]
    rfl
  refine ⟨⟨?_, ?_⟩, _root_.GlobalTheory.theta_ne_zero hτ 0 0⟩
  · simpa only [e] using hd
  · intro n n' z
    have := hq n n' z
    beta_reduce at this
    rw [e, e, Nat.cast_one] at this
    exact this

end GlobalTheory
end

