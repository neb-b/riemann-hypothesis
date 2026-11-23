module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0231

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylExtremalReproducingNormSqOne
section
open GlobalTheory.DualWeyl MvPolynomial NumberField MeasureTheory
open scoped Matrix ComplexConjugate InnerProductSpace

namespace GlobalTheory.DualWeyl.Repro

variable {N : ℕ} {la : Fin N → ℕ}

theorem exists_repr (la : Fin N → ℕ) :
    ∃ k : nabla la ℂ, ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1 := by
  have : CompleteSpace (Space la) := FiniteDimensional.complete ℂ _
  refine ⟨(toSpace la).symm ((InnerProductSpace.toDual ℂ (Space la)).symm
    (LinearMap.toContinuousLinearMap (evSpace la 1))), fun f => ?_⟩
  rw [← inner_toSpace, LinearEquiv.apply_symm_apply, InnerProductSpace.toDual_symm_apply]
  rfl

theorem form_rhoU_repr {k : nabla la ℂ} (hk : ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1)
    (u : UN N) (f : nabla la ℂ) :
    form la f.1 (rhoU la u⁻¹ k : Pol N ℂ) = evalAt u.1ᵀ f.1 := by
  rw [← form_rhoU u, Representation.self_inv_apply, hk, rhoU_apply, evalAt_rho, Matrix.mul_one]

theorem normSq_repr (hla : Antitone la) {k : nabla la ℂ}
    (hk : ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1) : normSq la k.1 = 1 := by
  let e : Idx la → nabla la ℂ := fun i => (toSpace la).symm (onBasis la i)
  have he : ∀ i, toSpace la (e i) = onBasis la i := fun i => (toSpace la).apply_symm_apply _
  have h1 : ∀ g : UN N, ∑ i, ‖evalAt g.1 (e i).1‖ ^ 2 = normSq la k.1 := by
    intro g
    let u : UN N := ⟨g.1ᵀ, transpose_mem_unitaryGroup g.2⟩
    rw [← normSq_rhoU u⁻¹, ← norm_toSpace_sq, ← (onBasis la).sum_sq_norm_inner_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← he, inner_toSpace, form_rhoU_repr hk]
    rfl
  have h2 : ∑ i, normSq la (e i).1 = dim la := by
    simp only [← norm_toSpace_sq, he, (onBasis la).orthonormal.1]
    simp [dim_eq_card]
  have h3 : ∑ i, normSq la (e i).1 = dim la * normSq la k.1 := by
    conv_lhs => simp only [normSq]
    rw [← Finset.mul_sum, ← integral_finsetSum _ fun i _ => integrable_norm_sq _]
    simp only [h1]
    simp
  have hd : (dim la : ℝ) ≠ 0 := by exact_mod_cast (dim_pos hla).ne'
  exact mul_left_cancel₀ hd (by rw [← h3, h2, mul_one])

theorem rowAct_diagonal_repr {k : nabla la ℂ}
    (hk : ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1) (t : Fin N → ℂ) (ht : ∀ a, ‖t a‖ = 1) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal t) k.1 = (∏ a, t a ^ la a) • k.1 := by
  have hu : Matrix.diagonal t ∈ Matrix.unitaryGroup (Fin N) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp [Complex.mul_conj', ht]
  let u : UN N := ⟨_, hu⟩
  have hinv : (u⁻¹).1ᵀ = Matrix.diagonal (star t) := by
    change (star (Matrix.diagonal t))ᵀ = _
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_transpose]
  have h : rhoU la u k = (∏ a, t a ^ la a) • k := by
    apply (toSpace la).injective
    refine ext_inner_right ℂ fun v => ?_
    obtain ⟨f, rfl⟩ := (toSpace la).surjective v
    rw [inner_toSpace, inner_toSpace, ← inv_inv u, form_rhoU_repr hk, hinv, Submodule.coe_smul, form_smul_right,
      hk, ← Matrix.one_mul (Matrix.diagonal (star t)), ← evalAt_colAct,
      colAct_of_mem f.2 _ (Matrix.blockTriangular_diagonal _), map_smul]
    simp [diagChar]
  have h' := congrArg Subtype.val h
  rwa [rhoU_apply, coe_rho, Matrix.diagonal_transpose] at h'

theorem isWeightedHomogeneous_of_torus {f : Pol N ℂ}
    (h : ∀ t : Fin N → ℂ, (∀ a, ‖t a‖ = 1) →
      Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal t) f = (∏ a, t a ^ la a) • f) :
    IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) f la := by
  classical
  intro m hm
  funext a
  rw [Formalism.GradedWeylDivisibility.ldrow_weight_rowW]
  have hn : Formalism.GradedWeylDivisibility.rowDeg m a + la a + 1 ≠ 0 := by omega
  have hz := Complex.isPrimitiveRoot_exp _ hn
  have hz1 := hz.norm'_eq_one hn
  generalize Complex.exp _ = z at hz hz1
  have h1 := congrArg (AddMonoidAlgebra.coeff · m) (h (Function.update 1 a z) fun b => by
    by_cases hb : b = a
    · subst hb; simpa using hz1
    · simp [Function.update_of_ne hb])
  rw [Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag, coeff_smul, smul_eq_mul, mul_comm] at h1
  have h2 := mul_right_cancel₀ hm h1
  have h3 : ∀ d : Fin N → ℕ, ∏ b, Function.update (1 : Fin N → ℂ) a z b ^ d b = z ^ d a := by
    intro d
    rw [Finset.prod_eq_single a]
    · simp
    · intro b _ hb
      simp [Function.update_of_ne hb]
    · simp
  rw [h3, h3] at h2
  exact hz.pow_inj (by omega) (by omega) h2

theorem extremal_reproducing : ∀ (N : ℕ) (la : Fin N → ℕ), Antitone la →
    (∀ f ∈ nabla la ℂ, form la f (extremal la ℂ) = evalAt 1 f) ∧ normSq la (extremal la ℂ) = 1 := by
  intro N la hla
  obtain ⟨k, hk⟩ := exists_repr la
  have h1 := normSq_repr hla hk
  have h2 : evalAt 1 k.1 = 1 := by rw [← hk, form_self, h1, Complex.ofReal_one]
  have h3 := GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight ℂ N la hla k.1 k.2 (isWeightedHomogeneous_of_torus (rowAct_diagonal_repr hk))
  rw [h2, one_smul] at h3
  rw [← h3]
  exact ⟨fun f hf => hk ⟨f, hf⟩, h1⟩

end GlobalTheory.DualWeyl.Repro
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicProperties
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

variable {Λ : AddSubgroup ℂ}

open NumberField Classical in
open scoped BigOperators in
variable {Λ : AddSubgroup ℂ} in
private lemma sgStar_add_lattice_eq_mul_exp (hΛ : _root_.GlobalTheory.EvenTheta.IsLat Λ) {a : ℂ} (ha : a ∈ Λ)
    (z : ℂ) :
    _root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ (z + a) = (if a / 2 ∈ Λ then 1 else -1) * _root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ z *
      Complex.exp (↑Real.pi * z * (starRingEnd ℂ) a / ↑(_root_.Formalism.MainNotions.TaylorLogMetric.area Λ) +
        ↑Real.pi * a * (starRingEnd ℂ) a / (2 * ↑(_root_.Formalism.MainNotions.TaylorLogMetric.area Λ))) := by
  have h := hΛ.sg_law ha z
  unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1 at h
  rw [← h, mul_assoc, ← Complex.exp_add]
  ring_nf <;> simp

open NumberField Classical in
open scoped BigOperators in
variable {Λ : AddSubgroup ℂ} in
private lemma mul_exp_eq_one_of_exp_relation {ε s x y w k : ℂ} (hs : s ≠ 0)
    (h : -1 * s * Complex.exp x = ε * (-1 * s * Complex.exp y) * Complex.exp w)
    (hk : y + w = x + k) : ε * Complex.exp k = 1 := by
  have h' : -1 * s * Complex.exp x = ε * (-1 * s * (Complex.exp x * Complex.exp k)) := by
    rw [← Complex.exp_add, ← hk, Complex.exp_add]
    linear_combination h
  have hprod : (s * Complex.exp x) * (ε * Complex.exp k - 1) = 0 := by
    linear_combination h'
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact absurd h0 (mul_ne_zero hs (Complex.exp_ne_zero x))
  · exact sub_eq_zero.1 h0

open NumberField Classical in
open scoped BigOperators in
variable {Λ : AddSubgroup ℂ} in
private lemma mul_mul_exp_eq_of_mul_exp_eq_one {ε k a s q : ℂ} (h : ε * Complex.exp k = 1) (hs : s = k + q) :
    ε * (a * Complex.exp s) = a * Complex.exp q := by
  rw [hs, Complex.exp_add]
  linear_combination (a * Complex.exp q) * h


open NumberField Classical in
open scoped BigOperators in
variable {Λ : AddSubgroup ℂ} in
theorem _root_.GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties : ∀ Λ : AddSubgroup ℂ, _root_.GlobalTheory.EvenTheta.IsLat Λ →
    ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → Differentiable ℂ (_root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀) ∧ _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ 0 = 1 ∧
    (∀ z, _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ (-z) = _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z) ∧
    (∀ z, _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z ^ 2 = _root_.GlobalTheory.EvenTheta.sqTh Λ t₀ z) ∧
    (∀ z, _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z = 0 ↔ z + t₀ ∈ Λ) ∧
    ∀ ω ∈ Λ, ω / 2 + t₀ ∉ Λ → ∀ z, _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ ω (_root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀) z = _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z := by
  intro Λ hΛ t ht h2t
  have hσt : _root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ t ≠ 0 := fun h => ht ((hΛ.sg_eq_zero t).1 h)
  have hhalf : ¬ (2 * t / 2 ∈ Λ) := by rwa [mul_div_cancel_left₀ t two_ne_zero]
  have hU0 : _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) 0 ≠ 0 := by
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1
    rw [zero_add]
    exact mul_ne_zero hσt (Complex.exp_ne_zero _)
  have hopp : ∀ y, _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ (-t) (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) y = -_root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) y := by
    intro y
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1
    rw [show y + t = y + -t + 2 * t by ring, sgStar_add_lattice_eq_mul_exp hΛ h2t, if_neg hhalf]
    simp only [mul_assoc, ← Complex.exp_add, map_neg, map_mul, map_ofNat]
    ring_nf
  have heven : ∀ z, _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) (-z) = _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) z := by
    intro z
    have h := hopp z
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1 at h ⊢
    rw [show -z + t = -(z + -t) by ring, hΛ.sg_neg]
    simp only [map_neg] at h ⊢
    ring_nf at h ⊢
    linear_combination -h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hd := hΛ.differentiable
    unfold _root_.Formalism.MainNotions.GL3Theta.th0 _root_.Formalism.MainNotions.TaylorLogMetric.U1
    fun_prop
  · unfold _root_.Formalism.MainNotions.GL3Theta.th0
    exact div_self hU0
  · intro z
    unfold _root_.Formalism.MainNotions.GL3Theta.th0
    rw [heven]
  · intro z
    have h := hΛ.sqTh_mul ht z
    rw [hopp, hopp] at h
    unfold _root_.Formalism.MainNotions.GL3Theta.th0
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hU0)]
    linear_combination h
  · intro z
    unfold _root_.Formalism.MainNotions.GL3Theta.th0
    rw [div_eq_zero_iff, or_iff_left hU0]
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1
    rw [mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), hΛ.sg_eq_zero]
  · intro ω hω hωt z
    have hsum : ¬ ((ω + 2 * t) / 2 ∈ Λ) := by
      rwa [show (ω + 2 * t) / 2 = ω / 2 + t by ring]
    have h1 := sgStar_add_lattice_eq_mul_exp hΛ (add_mem hω h2t) t
    have h2 := sgStar_add_lattice_eq_mul_exp hΛ hω (t + 2 * t)
    have h3 := sgStar_add_lattice_eq_mul_exp hΛ h2t t
    rw [if_neg hsum] at h1
    rw [if_neg hhalf] at h3
    rw [show t + 2 * t + ω = t + (ω + 2 * t) by ring, h1, h3] at h2
    have hε := mul_exp_eq_one_of_exp_relation
      (k := (↑Real.pi * t * (starRingEnd ℂ) ω - ↑Real.pi * ω * (starRingEnd ℂ) t) /
        ↑(_root_.Formalism.MainNotions.TaylorLogMetric.area Λ)) hσt h2 (by simp only [map_add (f := _), map_mul, map_ofNat]; ring)
    unfold _root_.Formalism.MainNotions.GL3Theta.th0 _root_.Formalism.MainNotions.TaylorLogMetric.U1
    beta_reduce
    rw [show z + ω + t = z + t + ω by ring, sgStar_add_lattice_eq_mul_exp hΛ hω, div_mul_eq_mul_div]
    congr 1
    simp only [mul_assoc, ← Complex.exp_add]
    exact mul_mul_exp_eq_of_mul_exp_eq_one hε (by ring)

end GlobalTheory.EvenTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEntireOfLocallyDvd
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter Topology

namespace GlobalTheory.EvenTheta

theorem exists_entire_of_locally_dvd {F S : ℂ → ℂ} (hS : Dense {z | S z ≠ 0})
    (h : ∀ w, ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ ∀ᶠ z in 𝓝 w, F z = S z * g z) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z, F z = S z * G z := by
  choose g hg hF using h
  refine ⟨fun w => g w w, fun w => ?_, fun z => (hF z).self_of_nhds⟩
  refine (hg w).differentiableAt.congr_of_eventuallyEq ?_
  filter_upwards [(hg w).eventually_analyticAt, (hF w).eventually_nhds] with z h1 h2
  refine tendsto_nhds_unique_of_frequently_eq (hg z).continuousAt h1.continuousAt ?_
  have h3 : ∃ᶠ y in 𝓝 z, S y ≠ 0 := mem_closure_iff_frequently.1 (hS z)
  refine (h3.and_eventually (h2.and (hF z))).mono fun y hy => ?_
  exact mul_left_cancel₀ hy.1 (hy.2.2.symm.trans hy.2.1)

theorem IsLat.exists_sg_add {Λ : AddSubgroup ℂ} (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) :
    ∃ c : ℂ → ℂ, Differentiable ℂ c ∧ ∀ z, sgStar Λ (z + ω) = c z * sgStar Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  rw [GlobalTheory.OddTheta.sgStar_eq L Λ hL]
  refine ⟨_, ?_, GlobalTheory.canonicalSigma_add L ((hL ω).1 hω)⟩
  unfold GlobalTheory.latticeForm
  fun_prop

theorem exists_eq_sg_sq_mul : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (k : ℕ) (F : ℂ → ℂ), Differentiable ℂ F → (∀ z, F (-z) = F z) → F 0 = 0 → (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * (k + 1)) = F z * sgStar Λ (z + ω) ^ (2 * (k + 1))) → ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ z, G (-z) = G z) ∧ (∀ z, F z = sgStar Λ z ^ 2 * G z) ∧ ∀ ω ∈ Λ, ∀ z, G (z + ω) * sgStar Λ z ^ (2 * k) = G z * sgStar Λ (z + ω) ^ (2 * k) := by
  intro Λ hΛ k F hF he h0 hlaw
  have hσ := hΛ.differentiable
  have hσc := hσ.continuous
  have hFc := hF.continuous
  have hne : ∀ z ∉ Λ, sgStar Λ z ≠ 0 := fun z hz => (hΛ.sg_eq_zero z).not.2 hz
  obtain ⟨h, hh, eh⟩ := GlobalTheory.exists_eq_add_sq_mul_of_even (hF.analyticAt 0) he
  have hu : AnalyticAt ℂ (dslope (sgStar Λ) 0) 0 :=
    (differentiableOn_univ.1
      ((Complex.differentiableOn_dslope univ_mem).2 hσ.differentiableOn)).analyticAt 0
  have hu0 : dslope (sgStar Λ) 0 0 ≠ 0 := by
    rw [dslope_same, (GlobalTheory.OddTheta.sgStar_laws Λ hΛ).1.2.1]
    exact one_ne_zero
  have eu : ∀ z, sgStar Λ z = z * dslope (sgStar Λ) 0 z := fun z => by
    have := sub_smul_dslope (sgStar Λ) 0 z
    rw [(hΛ.sg_eq_zero 0).2 Λ.zero_mem] at this
    simpa using this.symm
  obtain ⟨G, hG, eG⟩ := exists_entire_of_locally_dvd (F := F) (S := fun z => sgStar Λ z ^ 2)
    (hΛ.dense_compl.mono fun z hz => pow_ne_zero 2 (hne z hz)) fun w => by
      by_cases hw : w ∈ Λ
      · obtain ⟨c, hc, ec⟩ := hΛ.exists_sg_add hw
        have hcc := hc.continuous
        have eF : ∀ z, F (z + w) = c z ^ (2 * (k + 1)) * F z := fun z => by
          refine congrFun (Continuous.ext_on hΛ.dense_compl (f := fun z => F (z + w))
            (g := fun z => c z ^ (2 * (k + 1)) * F z) (by fun_prop) (by fun_prop) fun z hz => ?_) z
          refine mul_right_cancel₀ (pow_ne_zero (2 * (k + 1)) (hne z hz)) ?_
          beta_reduce
          rw [hlaw w hw, ec]
          ring
        have hs : AnalyticAt ℂ (fun y : ℂ => y - w) w := by fun_prop
        have ha : AnalyticAt ℂ
            (fun z => c z ^ (2 * k) * h z / dslope (sgStar Λ) 0 z ^ 2) 0 :=
          (((hc.analyticAt 0).pow _).mul hh).div (hu.pow 2) (pow_ne_zero 2 hu0)
        refine ⟨_, ha.comp_of_eq hs (sub_self w), ?_⟩
        filter_upwards [(hu.comp_of_eq hs (sub_self w)).continuousAt.eventually_ne
          (y := 0) (by simpa using hu0)] with y hy
        obtain ⟨z, rfl⟩ : ∃ z, y = z + w := ⟨y - w, by ring⟩
        simp only [Function.comp, add_sub_cancel_right] at hy ⊢
        rw [eF, ec, eh, h0, eu z]
        field_simp
        ring
      · refine ⟨fun z => F z / sgStar Λ z ^ 2, (hF.analyticAt w).div ((hσ.analyticAt w).pow 2)
          (pow_ne_zero 2 (hne w hw)), ?_⟩
        filter_upwards [hσc.continuousAt.eventually_ne (hne w hw)] with y hy
        field_simp
  have hGc := hG.continuous
  refine ⟨G, hG, fun z => ?_, eG, fun ω hω z => ?_⟩
  · refine congrFun (Continuous.ext_on hΛ.dense_compl (f := fun z => G (-z)) (by fun_prop) hGc
      fun z hz => ?_) z
    refine mul_left_cancel₀ (pow_ne_zero 2 (hne z hz)) ?_
    have h1 := eG (-z)
    rw [he, hΛ.sg_neg, neg_sq] at h1
    exact h1.symm.trans (eG z)
  · refine congrFun (Continuous.ext_on hΛ.dense_compl
      (f := fun z => G (z + ω) * sgStar Λ z ^ (2 * k))
      (g := fun z => G z * sgStar Λ (z + ω) ^ (2 * k)) (by fun_prop) (by fun_prop)
      fun z hz => ?_) z
    have hz' : z + ω ∉ Λ := fun h' => hz (by simpa using Λ.sub_mem h' hω)
    refine mul_left_cancel₀
      (mul_ne_zero (pow_ne_zero 2 (hne z hz)) (pow_ne_zero 2 (hne _ hz'))) ?_
    have h1 := hlaw ω hω z
    rw [eG z, eG (z + ω)] at h1
    beta_reduce at h1 ⊢
    linear_combination h1

end GlobalTheory.EvenTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteAdeleExtendedCharacterOfCurve
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.AdelicChar

theorem ee_add (s t : ℝ) : ee (s + t) = ee s * ee t := by
  rw [ee, ee, ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ee_int (k : ℤ) : ee k = 1 := by
  rw [ee, mul_comm]
  exact_mod_cast Complex.exp_int_mul_two_pi_mul_I k

variable (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)

theorem cmTraceAdditiveCharacter_add (a b : D.host.E) : psi0 D cc δ (a + b) = psi0 D cc δ a * psi0 D cc δ b := by
  rw [psi0, psi0, psi0, ← ee_add]
  congr 1
  simp only [map_add (f := _), Finset.sum_add_distrib, Complex.add_im]
  ring

theorem cmTraceAdditiveCharacter_zero : psi0 D cc δ 0 = 1 := by simp [psi0, ee]

theorem embT_conj (τ : D.what₂.Tau) (a : D.host.E) :
    embT D τ (D.host.conj a) = (starRingEnd ℂ) (embT D τ a) := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have h : D.host.conj a = IsCMField.complexConj D.host.E a := by
    apply D.host.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj]
    exact D.host.toHostAx.conjE_apply _ a
  rw [h, IsCMField.complexEmbedding_complexConj]

theorem cmTraceAdditiveCharacter_add_conj (a : D.host.E) : psi0 D cc δ (a + D.host.conj a) = 1 := by
  have : (∑ τ, embT D τ (a + D.host.conj a)).im = 0 := by
    simp [Complex.im_sum, embT_conj]
  rw [psi0, this]
  simp [ee]

theorem im_div_area (hcc : cc ≠ ⊥) (hδ : δ ≠ 0) {x y : ℂ} (hx : x ∈ lamOf D cc δ) (hy : y ∈ lamOf D cc δ) :
    ∃ k : ℤ, (x * (starRingEnd ℂ) y).im / area (lamOf D cc δ) = k := by
  obtain ⟨a, τ, ha, -, h⟩ := GlobalTheory.CurveLattice.exists_tau D cc hcc
  have hda : δ * a ≠ 0 := mul_ne_zero hδ ha
  rw [GlobalTheory.CurveLattice.area_of_tau hda (h δ)]
  obtain ⟨m, n, rfl⟩ := (h δ x).1 hx
  obtain ⟨m', n', rfl⟩ := (h δ y).1 hy
  refine ⟨m * n' - n * m', ?_⟩
  have hp : 0 < ‖δ * a‖ ^ 2 * τ.im := by
    have := norm_pos_iff.2 hda
    have := τ.im_pos
    positivity
  rw [div_eq_iff hp.ne']
  generalize δ * a = b
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem cmTraceAdditiveCharacter_trivial_multiple_integers (hg : admG1 D) (hc : Crv D cc δ) :
    ∃ m : ℕ, 0 < m ∧ ∀ r : D.host.E, IsIntegral ℤ r → psi0 D cc δ ((m : D.host.E) * r) = 1 := by
  have hδ : δ ≠ 0 := (GlobalTheory.CurveLattice.lattice_of_curve D hg cc δ hc).2.1
  have hcc := hc.1.1
  set n := Ideal.absNorm cc with hn
  have hn0 : n ≠ 0 := by simpa [hn, Ideal.absNorm_eq_zero_iff] using hcc
  refine ⟨n * n, by positivity, fun r hr => ?_⟩
  let t : 𝓞 D.host.K := ⟨Algebra.trace D.host.K D.host.E r, Algebra.isIntegral_trace hr⟩
  have hnc : (n : 𝓞 D.host.K) ∈ cc := Ideal.absNorm_mem cc
  obtain ⟨k, hk⟩ := im_div_area D cc δ hcc hδ
    ((GlobalTheory.CurveLattice.mem_lamOf D cc δ _).2 ⟨_, cc.mul_mem_right t hnc, rfl⟩)
    ((GlobalTheory.CurveLattice.mem_lamOf D cc δ _).2 ⟨_, hnc, rfl⟩)
  rw [psi0, ← ee_int (-k)]
  congr 1
  have h1 : ∑ τ, embT D τ (((n * n : ℕ) : D.host.E) * r) =
      (n : ℂ) * n * D.host.φ₀ ((t : D.host.K) : D.host.E) := by
    have := hg.2 r
    simp only [map_mul, map_natCast, ← Finset.mul_sum, this, Nat.cast_mul]
    rfl
  have h2 : D.host.φ₀ (((n * t : 𝓞 D.host.K) : D.host.K) : D.host.E) =
      (n : ℂ) * D.host.φ₀ ((t : D.host.K) : D.host.E) := by simp
  have h3 : D.host.φ₀ ((((n : ℕ) : 𝓞 D.host.K) : D.host.K) : D.host.E) = (n : ℂ) := by simp
  rw [h2, h3] at hk
  rw [h1, Int.cast_neg, ← hk]
  generalize D.host.φ₀ ((t : D.host.K) : D.host.E) = z
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem exists_rat (m : ℕ) (hm : 0 < m) (y : AE D) :
    ∃ e : D.host.E, ∃ s ∈ OhE D, y = inc D e + (m : AE D) * s := by
  obtain ⟨n, hn, hy⟩ := GlobalTheory.HeckeVal.exists_denom D y
  obtain ⟨r, -, w, hw, e⟩ := GlobalTheory.HeckeVal.exists_approx D (n * m) (Nat.mul_pos hn hm) _ hy
  have h1 : inc D ((n : D.host.E)⁻¹) * (n : AE D) = 1 := by
    rw [← map_natCast (inc D), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), map_one]
  refine ⟨(n : D.host.E)⁻¹ * r, w, hw, ?_⟩
  rw [map_mul]
  push_cast at e
  linear_combination inc D ((n : D.host.E)⁻¹) * e + ((m : AE D) * w - y) * h1

theorem exists_psi : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ ψ : AE D → ℂ, IsPsi D cc δ ψ := by
  intro D hg cc δ hc
  obtain ⟨m, hm, hint⟩ := cmTraceAdditiveCharacter_trivial_multiple_integers D cc δ hg hc
  choose e s hs he using exists_rat D m hm
  have key : ∀ (y : AE D) (a : D.host.E) (w : AE D), w ∈ OhE D → y = inc D a + (m : AE D) * w →
      psi0 D cc δ (e y) = psi0 D cc δ a := by
    intro y a w hw h
    have hm' : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h1 : inc D ((m : D.host.E)⁻¹) * (m : AE D) = 1 := by
      rw [← map_natCast (inc D), ← map_mul, inv_mul_cancel₀ hm', map_one]
    have h2 : inc D ((m : D.host.E)⁻¹ * (e y - a)) = w - s y := by
      rw [map_mul, map_sub]
      linear_combination inc D ((m : D.host.E)⁻¹) * (h - he y) + (w - s y) * h1
    have h3 := hint _ ((GlobalTheory.HeckeVal.inc_mem_iff D _).1 (h2 ▸ sub_mem hw (hs y)))
    rw [mul_inv_cancel_left₀ hm'] at h3
    rw [show e y = a + (e y - a) by ring, cmTraceAdditiveCharacter_add, h3, mul_one]
  refine ⟨fun y => psi0 D cc δ (e y), fun x y => ?_, ?_, fun a => ?_, fun y => ?_, m, hm, fun w hw => ?_⟩
  · rw [← cmTraceAdditiveCharacter_add]
    refine key _ _ _ (add_mem (hs x) (hs y)) ?_
    rw [map_add (f := _)]
    linear_combination he x + he y
  · exact (key 0 0 0 (zero_mem _) (by simp)).trans (cmTraceAdditiveCharacter_zero D cc δ)
  · exact key _ a 0 (zero_mem _) (by simp)
  · have hw : sgA D (s y) ∈ OhE D := Formalism.UG.P.csDual_sig_mem _ (hs y)
    refine (key _ (e y + D.host.conj (e y)) _ (add_mem (hs y) hw) ?_).trans (cmTraceAdditiveCharacter_add_conj D cc δ _)
    have h := congrArg (sgA D) (he y)
    rw [map_add (f := _), map_mul, map_natCast, GlobalTheory.NormSum.PtsMem.sgA_inc] at h
    rw [map_add (f := _)]
    linear_combination he y + h
  · exact (key _ 0 w hw (by simp)).trans (cmTraceAdditiveCharacter_zero D cc δ)

end GlobalTheory.FinWeil.AdelicChar
end

