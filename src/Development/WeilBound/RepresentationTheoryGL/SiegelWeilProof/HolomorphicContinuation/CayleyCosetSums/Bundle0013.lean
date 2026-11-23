module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0012
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DpDual
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ContinuousQuad
section
noncomputable section

open Matrix Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.HolTPf

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

def imM (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (-(Complex.I / 2)) • (Z - Zᴴ)

theorem star_c : star (-(Complex.I / 2)) = -(-(Complex.I / 2)) := by
  apply Complex.ext <;> simp <;> norm_num

theorem imM_herm (Z : Matrix (Fin n) (Fin n) ℂ) : (imM Z).IsHermitian := by
  unfold imM
  rw [IsHermitian, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, star_c, neg_smul,
    ← smul_neg, neg_sub]

theorem mem_dom_iff (Z : Fin n → Fin n → ℂ) : Z ∈ Dom n ↔ (imM (Matrix.of Z)).PosDef := Iff.rfl

theorem posdef_iff_re {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    M.PosDef ↔ ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (M *ᵥ x)).re := by
  rw [posDef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨-, h⟩ x hx
    exact (Complex.lt_def.1 (h hx)).1
  · intro h
    refine ⟨hM, fun x hx => ?_⟩
    have him : (star x ⬝ᵥ (M *ᵥ x)).im = 0 := hM.im_star_dotProduct_mulVec_self x
    exact Complex.lt_def.2 ⟨h x hx, by simpa using him.symm⟩

theorem re_smul_quad (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (c : ℝ) :
    (star ((c : ℂ) • x) ⬝ᵥ (M *ᵥ ((c : ℂ) • x))).re = c ^ 2 * (star x ⬝ᵥ (M *ᵥ x)).re := by
  rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem continuous_quad : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) =>
    (star p.2 ⬝ᵥ (imM (Matrix.of p.1) *ᵥ p.2)).re := by
  have h1 : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) => (Matrix.of p.1 : Matrix (Fin n) (Fin n) ℂ) :=
    continuous_fst
  have h2 : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) => imM (Matrix.of p.1) := by
    unfold imM
    exact (h1.sub h1.matrix_conjTranspose).const_smul (-(Complex.I / 2) : ℂ)
  exact Complex.continuous_re.comp (continuous_snd.star.dotProduct (h2.matrix_mulVec continuous_snd))

theorem isOpen_dom' : IsOpen (Dom n) := by
  rw [isOpen_iff_mem_nhds]
  intro Z hZ
  have hsph : IsCompact (Metric.sphere (0 : Fin n → ℂ) 1) := isCompact_sphere 0 1
  have key : ∀ᶠ W in 𝓝 Z, ∀ y ∈ Metric.sphere (0 : Fin n → ℂ) 1,
      0 < (star y ⬝ᵥ (imM (Matrix.of W) *ᵥ y)).re := by
    apply hsph.eventually_forall_of_forall_eventually
    intro y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy
    have hpos : 0 < (star y ⬝ᵥ (imM (Matrix.of Z) *ᵥ y)).re :=
      (posdef_iff_re (imM_herm _)).1 ((mem_dom_iff Z).1 hZ) y hy0
    exact (continuous_quad.tendsto (Z, y)).eventually (lt_mem_nhds hpos)
  filter_upwards [key] with W hW
  rw [mem_dom_iff, posdef_iff_re (imM_herm _)]
  intro x hx
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hy : (((‖x‖⁻¹ : ℝ) : ℂ) • x) ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul]
    simp [hn.ne']
  have hxe : x = ((‖x‖ : ℝ) : ℂ) • (((‖x‖⁻¹ : ℝ) : ℂ) • x) := by
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  rw [hxe, re_smul_quad]
  exact mul_pos (pow_pos hn 2) (hW _ hy)

theorem convex_dom' : Convex ℝ (Dom n) := by
  intro Z hZ W hW a b ha hb hab
  rw [mem_dom_iff, posdef_iff_re (imM_herm _)] at hZ hW ⊢
  intro x hx
  have hm : imM (Matrix.of (a • Z + b • W)) = (a : ℂ) • imM (Matrix.of Z) + (b : ℂ) • imM (Matrix.of W) := by
    ext i j
    simp [imM, Complex.real_smul]
    ring
  have hq : (star x ⬝ᵥ (imM (Matrix.of (a • Z + b • W)) *ᵥ x)).re
      = a * (star x ⬝ᵥ (imM (Matrix.of Z) *ᵥ x)).re + b * (star x ⬝ᵥ (imM (Matrix.of W) *ᵥ x)).re := by
    rw [hm, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, dotProduct_smul, Complex.add_re, smul_eq_mul, smul_eq_mul, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
  rw [hq]
  have hp := hZ x hx
  have hq' := hW x hx
  rcases ha.eq_or_lt with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hq'
  · linarith [mul_pos ha' hp, mul_nonneg hb hq'.le]

private theorem conjTranspose_I_smul_add_sub_eq_neg_two_I (A B C D : Matrix (Fin n) (Fin n) ℂ)
    (h1 : -(Cᴴ * A) + Aᴴ * C = 0) (h2 : -(Cᴴ * B) + Aᴴ * D = 1)
    (h3 : -(Dᴴ * A) + Bᴴ * C = -1) (h4 : -(Dᴴ * B) + Bᴴ * D = 0) :
    (Complex.I • A + B)ᴴ * (Complex.I • C + D) - (Complex.I • C + D)ᴴ * (Complex.I • A + B)
      = (-(2 * Complex.I)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp only [conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  linear_combination (norm := skip) h1 + h4 + (-Complex.I) • h2 + Complex.I • h3
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

private theorem posDef_imM_mul_inv_of_skew_relation (X U : Matrix (Fin n) (Fin n) ℂ)
    (hk : Xᴴ * U - Uᴴ * X = (-(2 * Complex.I)) • (1 : Matrix (Fin n) (Fin n) ℂ)) :
    (imM (X * U⁻¹)).PosDef := by
  have hker : ∀ v, U *ᵥ v = 0 → v = 0 := by
    intro v hv
    have e : star v ⬝ᵥ ((Xᴴ * U - Uᴴ * X) *ᵥ v)
        = star v ⬝ᵥ (((-(2 * Complex.I)) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) := by
      rw [hk]
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero,
      zero_sub, dotProduct_neg, dotProduct_mulVec, ← star_mulVec, hv, star_zero, zero_dotProduct,
      neg_zero, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at e
    have h2I : -(2 * Complex.I) ≠ 0 := by simp
    have hvv : star v ⬝ᵥ v = 0 := (mul_eq_zero.1 e.symm).resolve_left h2I
    exact dotProduct_star_self_eq_zero.1 hvv
  have hinj : Function.Injective U.mulVec := by
    intro v w hvw
    have h0 : U *ᵥ (v - w) = 0 := by
      rw [Matrix.mulVec_sub, sub_eq_zero]
      exact hvw
    exact sub_eq_zero.1 (hker _ h0)
  have hU : IsUnit U := mulVec_injective_iff_isUnit.1 hinj
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).1 hU)
  have hc : (U⁻¹)ᴴ * Uᴴ = 1 := by
    rw [← conjTranspose_mul, hUU, conjTranspose_one]
  have e1 : X * U⁻¹ - (X * U⁻¹)ᴴ = (U⁻¹)ᴴ * (Uᴴ * X - Xᴴ * U) * U⁻¹ := by
    rw [conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc (U⁻¹)ᴴ Uᴴ X, hc,
      Matrix.one_mul, ← Matrix.mul_assoc (U⁻¹)ᴴ Xᴴ U, Matrix.mul_assoc _ U U⁻¹, hUU, Matrix.mul_one]
  have e2 : Uᴴ * X - Xᴴ * U = (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← neg_sub, hk, neg_smul, neg_neg]
  have e3 : imM (X * U⁻¹) = (U⁻¹)ᴴ * 1 * U⁻¹ := by
    unfold imM
    rw [e1, e2, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    have hs : -(Complex.I / 2) * (2 * Complex.I) = 1 := by
      ring_nf
      simp [Complex.I_sq]
    rw [hs, one_smul]
  have hinv : Function.Injective (U⁻¹).mulVec := by
    intro v w hvw
    have := congrArg (fun z => U *ᵥ z) hvw
    simpa [Matrix.mulVec_mulVec, hUU] using this
  rw [e3]
  exact Matrix.PosDef.one.conjTranspose_mul_mul_same hinv

theorem zOf_mem' (y : GR n) : zOf y ∈ Dom n := by
  have hM : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  have hblk : mR y = fromBlocks (toBlocks₁₁ (mR y)) (toBlocks₁₂ (mR y)) (toBlocks₂₁ (mR y))
      (toBlocks₂₂ (mR y)) :=
    (fromBlocks_toBlocks _).symm
  rw [hblk, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at hM
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul, add_zero, zero_add] at hM
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 hM
  have hk := conjTranspose_I_smul_add_sub_eq_neg_two_I _ _ _ _ h1 h2 h3 h4
  refine (mem_dom_iff (n := n) (zOf y)).2 ?_
  exact posDef_imM_mul_inv_of_skew_relation _ _ hk

theorem neg_conj_mem' {W : Fin n → Fin n → ℂ} (hW : W ∈ Dom n) :
    (-(Matrix.of W)ᴴ : Matrix (Fin n) (Fin n) ℂ) ∈ Dom n := by
  have h : imM (Matrix.of (-(Matrix.of W)ᴴ : Matrix (Fin n) (Fin n) ℂ)) = imM (Matrix.of W) := by
    change imM (-(Matrix.of W)ᴴ) = imM (Matrix.of W)
    ext i j
    simp [imM]
    ring
  refine (mem_dom_iff (n := n) (-(Matrix.of W)ᴴ : Matrix (Fin n) (Fin n) ℂ)).2 ?_
  rw [h]
  exact (mem_dom_iff W).1 hW

end PositivityTheory.Rg.Sw.HSt.HolTPf
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseFirstBlockEqAdjoint
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem inverse_first_block_eq_adjoint {x : M2 n} (hx : InG x) : ub1 x = (u1 x)ᴴ := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have hJ : JJ n * JJ n = -1 := by
    simp [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  have hl : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    have e : JJ n * xᴴ * JJ n * x = JJ n * (xᴴ * JJ n * x) := by simp only [Matrix.mul_assoc]
    rw [neg_mul, e, hx', hJ, neg_neg]
  rw [ub1, Matrix.inv_eq_left_inv hl, u1]
  rw [← fromBlocks_toBlocks x]
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg, toBlocks_fromBlocks₁₁,
    toBlocks_fromBlocks₂₁, conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I]
  simp
  abel

theorem secFz : SecFz := by
  intro n m e w y
  have hg : InG (mR y) := y.2
  have key : ∀ r : ℝ, 0 ≤ r → ((r⁻¹ : ℝ) : ℂ) ^ w = (r : ℂ) ^ (-w) := by
    intro r hr
    rw [Complex.ofReal_inv, Complex.inv_cpow, Complex.cpow_neg]
    rw [Complex.arg_ofReal_of_nonneg hr]
    exact Real.pi_ne_zero.symm
  simp only [fz, F0, f0, hLoc, inverse_first_block_eq_adjoint hg, det_conjTranspose]
  rw [key _ (by positivity), Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LamTrace
section
noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Main

variable {Kg : Type} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
  [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
  (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (m : ℕ) (e : ℤ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ)
  (hψc : HasCompactSupport ψ) {a b : M2 n} (ha : InG a) (hb : InG b)

include hι hK hψ hψc ha hb in
theorem Lam_trace (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    abelian₂ μ ι m e ψ a b z X = abelian₂ μ ι m e ψ a b z 1 / n * star X.trace := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun Y => star (abelian₂ μ ι m e ψ a b z Y)
      map_add' := fun Y W => by simp [Lam_add μ ι hι hK m e hψ hψc ha hb]
      map_smul' := fun c Y => by simp [Lam_smul, mul_comm] }
  have h := inv_trace L (fun U Y hU hY => by
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Lam_inv μ ι hK m e ha hb z hU hY]) X
  simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at h
  have h' := congrArg star h
  rw [star_star] at h'
  rw [h']
  simp [star_div₀, mul_comm]

include hι hK hψ hψc ha hb in
theorem Lam_diff : Differentiable ℂ fun z => abelian₂ μ ι m e ψ a b z 1 := by
  have hιK : ∀ k, InK (ι k) := ιK ι hK
  have hιG : ∀ k, InG (ι k) := fun k => (hιK k).1
  have hb21 : Continuous fun x : M2 n => toBlocks₂₁ x :=
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inr i))
  have hb22 : Continuous fun x : M2 n => toBlocks₂₂ x :=
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply (Sum.inr j)).comp (continuous_apply (Sum.inr i))
  have hu1 : Continuous fun x : M2 n => u1 x := by
    show Continuous fun x : M2 n => Complex.I • toBlocks₂₁ x + toBlocks₂₂ x
    exact (hb21.const_smul Complex.I).add hb22
  have hu2 : Continuous fun x : M2 n => u2 x := by
    show Continuous fun x : M2 n => -(Complex.I • toBlocks₂₁ x) + toBlocks₂₂ x
    exact (hb21.const_smul Complex.I).neg.add hb22
  have hR : (rhoP ⇑ι m e 1) = fun k =>
      star ((det (ι k) ^ e * (u1 (ι k)).det ^ (-(m : ℤ))) * ((u2 (ι k))ᴴ * u1 (ι k)).trace) := by
    funext k
    rw [rhoP, Matrix.mul_one, Matrix.inv_eq_left_inv (second_cayley_block_compact_unitary (hιK k))]
    simp [fz]
  have hRc : Continuous (rhoP ⇑ι m e 1) := by
    rw [hR]
    refine Continuous.star (Continuous.mul (Continuous.mul ?_ ?_) ?_)
    · exact hι.matrix_det.zpow₀ e fun k => Or.inl (LoweringDerivative.isUnit_det_of_inG (hιG k)).ne_zero
    · exact (hu1.comp hι).matrix_det.zpow₀ _ fun k => Or.inl (det_first_block_ne_zero_group (hιG k))
    · exact (((hu2.comp hι).matrix_conjTranspose).matrix_mul (hu1.comp hι)).matrix_trace
  have hH : Continuous fun p : Kg × ℂ => Hf m e ψ a b p.2 (ι p.1) := by
    have h1 := continuous_Hf m e hψ hψc ha hb
    refine h1.comp (f := fun p : Kg × ℂ => ((⟨ι p.1, hιG p.1⟩ : Gs n), p.2)) ?_
    refine Continuous.prodMk ?_ continuous_snd
    refine Continuous.subtype_mk ?_ _
    exact hι.comp continuous_fst
  set G : Kg → ℂ → ℂ := fun k w => rhoP ⇑ι m e 1 k * Hf m e ψ a b w (ι k) with hGdef
  have hG : Continuous (Function.uncurry G) := (hRc.comp continuous_fst).mul hH
  have hGd : ∀ k, Differentiable ℂ (G k) := fun k =>
    (differentiable_Hf m e hψ hψc ha hb (hιG k)).const_mul _
  have hLam : (fun z => abelian₂ μ ι m e ψ a b z 1) = fun z => ∫ k, G k z ∂μ := by
    funext z
    rw [Lam_eq]
  rw [hLam]
  intro z0
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall z0 2)).exists_bound_of_continuousOn
    hG.continuousOn
  have hbd : ∀ k, ∀ z ∈ Metric.ball z0 1, ‖deriv (G k) z‖ ≤ C := by
    intro k z hz
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 1) (C := C) one_pos
      (hGd k).diffContOnCl (fun w hw => by
        apply hC (k, w)
        refine ⟨Set.mem_univ _, ?_⟩
        rw [Metric.mem_closedBall]
        rw [Metric.mem_sphere] at hw
        rw [Metric.mem_ball] at hz
        linarith [dist_triangle w z z0])
    simpa using this
  have hmeas : Measurable fun k => deriv (G k) z0 :=
    by
    have hm := measurable_deriv_with_param (𝕜 := ℂ) (F := ℂ) (f := G) hG
    exact hm.comp (f := fun k : Kg => (k, z0)) (measurable_id.prodMk measurable_const)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := fun z k => G k z)
    (F' := fun z k => deriv (G k) z) (x₀ := z0) (bound := fun _ => C)
    (Metric.ball_mem_nhds z0 one_pos)
    (Filter.Eventually.of_forall fun z => (hG.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (integrable_integrand μ ι hι hK m e hψ hψc ha hb z0 1)
    hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k z hz => hbd k z hz)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k z _ => ((hGd k) z).hasDerivAt)
  exact key.2.differentiableAt

end Main

theorem lt2 : MultiplicityOneTestOperators := by
  intro n m e Kg _ _ _ _ _ _ μ _ ι hι hK ψ a b hψ hψc ha hb
  refine ⟨fun z => -(abelian₂ μ ι m e ψ a b z 1 / n), ?_, ?_⟩
  · exact ((Lam_diff μ ι hι hK m e hψ hψc ha hb).div_const _).neg
  · intro Y z x hx
    obtain ⟨p, k, hp, hk, hpk⟩ := AbsSt.iwa n (AbsSt.mkGR x hx)
    have hxe : x = mR p * mR k := by
      have h := congrArg mR hpk
      rw [AbsSt.mR_mkGR] at h
      rw [h]
      rfl
    obtain ⟨k1, hk1⟩ := (hK (mR k)).mp hk
    have hpG : InG (mR p) := p.2
    have hk1K : InK (ι k1) := hk1 ▸ hk
    rw [hxe, ← hk1, tOp_formula μ ι hK m e ψ ha hb hpG hp k1 Y z]
    change lam m e z (mR p) * fz m e 0 (ι k1) *
      abelian₂ μ ι m e ψ a b z (u2 (ι k1) * Y * (u1 (ι k1))⁻¹) = _
    rw [Lam_trace μ ι hι hK m e hψ hψc ha hb, eQ, fz_up hpG hp hk1K.1, Om_up hpG hp hk1K.1,
      fz_K m e z hk1K, Om_K hk1K, Matrix.inv_eq_left_inv (first_cayley_block_compact_unitary hk1K),
      Matrix.inv_eq_left_inv (second_cayley_block_compact_unitary hk1K)]
    have htr : star (u2 (ι k1) * Y * (u1 (ι k1))ᴴ).trace = ((u2 (ι k1))ᴴ * u1 (ι k1) * Yᴴ).trace := by
      rw [← Matrix.trace_conjTranspose, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
        ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    rw [htr]
    simp only [Matrix.neg_mul, Matrix.mul_smul, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul,
      ← Matrix.mul_assoc]
    ring

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

namespace PositivityTheory.Rg.Sw.HSt

theorem lt2 : MultiplicityOneTestOperators := CompactCayleyBlocks.lt2

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocSec
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def zOfE (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := (Complex.I • x.toBlocks₁₁ + x.toBlocks₁₂) * (u1 x)⁻¹

def LocSec : Prop :=
  ∀ (n : ℕ) (Z₀ : Matrix (Fin n) (Fin n) ℂ), ((-(Complex.I / 2)) • (Z₀ - Z₀ᴴ)).PosDef →
    ∃ s : Matrix (Fin n) (Fin n) ℂ → M2 n, (∀ᶠ Z in 𝓝 Z₀, InG (s Z) ∧ (s Z).det ≠ 0 ∧ zOfE (s Z) = Z) ∧
      ContDiffAt ℝ 1 s Z₀

def Fib : Prop :=
  ∀ (n : ℕ) (y y' : GR n), zOfE (mR y) = zOfE (mR y') → InK (mR (y⁻¹ * y'))

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.RcCongr
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

structure HD (m n : ℕ) (e : ℤ) (G : Type) [Group G] [TopologicalSpace G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ)
    (Ht : G → ℝ≥0) (f : G → ℂ) (U : Set ℂ) (d : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ) : Prop where
  ιc : Continuous ι
  split : ∀ g, ∃ (x : G) (y : GR n) (S : ℂ) (r : ℝ), 0 < r ∧ g = x * ι y ∧
    ∀ y' : GR n, (Ht (x * ι y') : ℝ) = r * hLoc y' ∧ f (x * ι y') = S * F0 m 0 e y'
  hU : IsOpen U
  hR : GlobalTheory.Cont.IsRightDomain U
  hs : s₀ ∈ U
  hol : ∀ g, DifferentiableOn ℂ (Ê · g) U
  cont : ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ)
  far : ∀ z : ℂ, t < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ c,
      ‖GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x) g c‖ ≤ u c) ∧
    ∀ g, Ê z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x) g

def ιK (n : ℕ) : KR n →* M2 n := (Units.coeHom (M2 n)).comp ((GR n).subtype.comp (KR n).subtype)

def resG {G : Type} [Group G] (ι : GR n →* G) (F : G → ℂ) (g : G) : M2 n → ℂ := lift fun y => F (g * ι y)

def FarId : Prop :=
  ∀ (m n : ℕ) (e : ℤ), 1 ≤ m → m < n →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0) (f : G → ℂ) (U : Set ℂ)
      (d : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ), HD m n e G Pp Γ ι s₀ Ht f U d Ê t → SecFz →
    ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
      (Q : Matrix (Fin n) (Fin n) ℂ) (N : ℕ) (ρ : Fin N → KR n → ℂ) (ψ : Fin N → (Fin n → Fin n → ℝ) → ℂ)
      (a b : Fin N → M2 n) (D : ℂ → ℂ) (M : Fin N → ℂ → ℂ), (∀ l, Continuous (ρ l)) → (∀ l, IsSingTest (ψ l)) →
      (∀ l, InG (a l) ∧ InG (b l)) → Differentiable ℂ D → (∀ l, Differentiable ℂ (M l)) →
      (∀ (z : ℂ) (x : M2 n), InG x →
        D z * rC (lowQ Q) (fz m e z) x = ∑ l, M l z * tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (fz m e z) x) →
      (∃ t' : ℝ, ∀ z : ℂ, t' < z.re → ∀ (g : G) (y : GR n),
        D (z - s₀) * rC (lowQ Q) (resG ι (Ê z) g) (mR y) =
          ∑ l, M l (z - s₀) * tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (resG ι (Ê z) g) (mR y)) ∧
      ∀ z ∈ U, ∀ (g : G) (y k : GR n), k ∈ KR n → Ê z (g * ι (y * k)) = Ê z (g * ι y) * F0 m 0 e k

def SmoothX : Prop :=
  ∀ (m n : ℕ) (e : ℤ), 1 ≤ m → m < n →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0) (f : G → ℂ) (U : Set ℂ)
      (d : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ), HD m n e G Pp Γ ι s₀ Ht f U d Ê t → ∀ g : G,
    ∃ (Φ : ℂ → M2 n → ℂ) (Ω : Set (M2 n)) (c : ℂ → ℂ), IsOpen Ω ∧ GSet n ⊆ Ω ∧ DifferentiableOn ℂ c U ∧ c s₀ ≠ 0 ∧
      (∀ z ∈ U, ∀ y : GR n, Φ z (mR y) = c z * Ê z (g * ι y)) ∧
      (∀ z ∈ U, ContDiffOn ℝ ∞ (Φ z) Ω) ∧
      (∀ r : ℕ, ContDiffOn ℝ ∞ (fun x => iteratedDeriv r (Φ · x) s₀) Ω) ∧
      (∀ x ∈ Ω, DifferentiableOn ℂ (Φ · x) U) ∧
      ∀ (Q : Matrix (Fin n) (Fin n) ℂ) (y : GR n),
        DifferentiableOn ℂ (fun z => rC (lowQ Q) (Φ z) (mR y)) U ∧
        ∀ r : ℕ, iteratedDeriv r (fun z => rC (lowQ Q) (Φ z) (mR y)) s₀ =
          rC (lowQ Q) (fun x => iteratedDeriv r (Φ · x) s₀) (mR y)

def TopHol : Prop :=
  ∀ (m n : ℕ) (e : ℤ), 1 ≤ m → m < n →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0) (f : G → ℂ) (U : Set ℂ)
      (d : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ), HD m n e G Pp Γ ι s₀ Ht f U d Ê t →
    ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
      (ρ : KR n → ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n), Continuous ρ → Continuous ψ → HasCompactSupport ψ →
      InG a → InG b → ∀ (g : G) (y : GR n),
      DifferentiableOn ℂ (fun z => tOp μ (ιK n) ρ ψ a b (resG ι (Ê z) g) (mR y)) U ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => tOp μ (ιK n) ρ ψ a b (resG ι (Ê z) g) (mR y)) s₀ =
        tOp μ (ιK n) ρ ψ a b (resG ι (fun x => iteratedDeriv r (Ê · x) s₀) g) (mR y)

def RcCongr : Prop :=
  ∀ (n : ℕ) (F F' : M2 n → ℂ) (Z : M2 n) (x : M2 n), InG x → (∀ x', InG x' → F x' = F' x') →
    (∀ t : ℝ, InG (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z))))) →
    (∀ t : ℝ, InG (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))))) → rC Z F x = rC Z F' x

end PositivityTheory.Rg.Sw.HSt
end
end

